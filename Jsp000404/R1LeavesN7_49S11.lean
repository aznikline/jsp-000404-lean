import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_49S7
import Jsp000404.R1LeavesN7_49S8
import Jsp000404.R1LeavesN7_49S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1337 | h1337
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1_x0 m hb0 hb1 hb3 hb4 h0 h1337
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1_x1 m hb0 hb1 hb3 hb4 h0 h1337

set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1 m hb0 hb1 hb3 hb4 h0

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_21_14_M_IR_L_I_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
            · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
              · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                  · linarith only [h0, h13, h16, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h13, h15, h16, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h10, h15, h19, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h1bigk with h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h14, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p21_1]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h10, h12, h13, h15, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h12, h13, h15, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      rcases p21_3 (m.d 0 1) (by simp) with h26 | h26
                      · rcases p21_3 (m.d 1 2) (by simp) with h27 | h27
                        · linarith only [h0, h27, hlam]
                        · linarith only [h27, h9, hlam]
                      · linarith only [h26, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h0, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h10, h12, h13, h15, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21_1]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h0, h12, h13, h15, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p21_1, u1ehi4]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h1, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h7, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h12, h13, h15, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21_1]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p21_1, u1ehi4]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h2, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h8, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h10, hlam, p21_1]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [hc14, hlam, hphi, p21_1, u1ehi4]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h3, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h9, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h11, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h12, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [hlam, p21_0]
              · linarith only [h0, h11, h13, h14, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
              · linarith only [h0, h10, h13, h52, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h54 | h54
                · rcases m.htr 3 4 5 (by decide) (by decide) with h55 | h55
                  · rcases h1bigk with h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h10, h52, h55, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p56_1]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h10, h52, h55, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p56_1]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      rcases p56_3 (m.d 0 1) (by simp) with h60 | h60
                      · rcases p56_3 (m.d 1 2) (by simp) with h61 | h61
                        · linarith only [h0, h61, hlam]
                        · linarith only [h61, h8, hlam]
                      · linarith only [h60, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      rcases p56_3 (m.d 0 1) (by simp) with h65 | h65
                      · rcases p56_3 (m.d 1 2) (by simp) with h66 | h66
                        · linarith only [h0, h66, hlam]
                        · linarith only [h66, h9, hlam]
                      · linarith only [h65, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h0, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h10, h52, h55, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p56_1]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p56_1, u1ehi3]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p56_1, u1ehi4]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h1, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h7, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hc13, hlam, hphi, p56_1, u1ehi3]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p56_1, u1ehi4]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h2, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h8, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h10, hlam, p56_1]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hc14, hlam, hphi, p56_1, u1ehi4]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h3, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h9, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h11, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h12, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hlam, p56_0]
                  · linarith only [h0, h54, h55, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h91 | h91
                  · linarith only [h0, h10, h54, h7, h91, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h10, h12, h13, h7, h91, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
            · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
              · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                · linarith only [h12, h96, hc24, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                  · linarith only [h0, h12, h7, h94, h98, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                  · rcases h1bigk with h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h7, h95, h98, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p100_1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      rcases p100_3 (m.d 0 1) (by simp) with h103 | h103
                      · rcases p100_3 (m.d 1 2) (by simp) with h104 | h104
                        · linarith only [h0, h104, hlam]
                        · linarith only [h104, h7, hlam]
                      · linarith only [h103, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      rcases p100_3 (m.d 0 1) (by simp) with h108 | h108
                      · rcases p100_3 (m.d 1 2) (by simp) with h109 | h109
                        · linarith only [h0, h109, hlam]
                        · linarith only [h109, h8, hlam]
                      · linarith only [h108, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      rcases p100_3 (m.d 0 1) (by simp) with h113 | h113
                      · rcases p100_3 (m.d 1 2) (by simp) with h114 | h114
                        · linarith only [h0, h114, hlam]
                        · linarith only [h114, h9, hlam]
                      · linarith only [h113, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h0, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hc12, hlam, hphi, p100_1, u1ehi2]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p100_1, u1ehi3]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h0, h12, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p100_1, u1ehi3]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h1, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h7, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hc13, hlam, hphi, p100_1, u1ehi3]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h0, h12, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p100_1, u1ehi3]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h2, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h8, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h10, hlam, p100_1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h12, hlam, p100_1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h3, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h9, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h11, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hc15, hlam, hphi, p100_1, u1ehi3]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hlam, p100_0]
              · linarith only [h0, h11, h7, h94, h95, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h139 | h139
              · linarith only [h0, h10, h139, h7, h94, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h141 | h141
                · linarith only [h0, h12, h141, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h143 | h143
                  · linarith only [h10, h12, h143, hlam]
                  · rcases h1bigk with h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h10, h7, h94, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p145_1]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h10, h94, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p145_1]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      rcases p145_3 (m.d 0 1) (by simp) with h149 | h149
                      · rcases p145_3 (m.d 1 2) (by simp) with h150 | h150
                        · linarith only [h0, h150, hlam]
                        · linarith only [h150, h8, hlam]
                      · linarith only [h149, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      rcases p145_3 (m.d 0 1) (by simp) with h154 | h154
                      · rcases p145_3 (m.d 1 2) (by simp) with h155 | h155
                        · linarith only [h0, h155, hlam]
                        · linarith only [h155, h9, hlam]
                      · linarith only [h154, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h0, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h11, h143, h94, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p145_1]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p145_1, u1ehi3]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h0, h12, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p145_1, u1ehi3]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h1, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h7, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [hc13, hlam, hphi, p145_1, u1ehi3]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h0, h12, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p145_1, u1ehi3]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h2, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h8, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h10, hlam, p145_1]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h12, hlam, p145_1]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h3, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h9, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h11, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [hc15, hlam, hphi, p145_1, u1ehi3]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [hlam, p145_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h179 | h179
          · linarith only [h10, h11, h179, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h181 | h181
            · rcases m.htr 2 3 5 (by decide) (by decide) with h182 | h182
              · linarith only [h11, h182, h7, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h184 | h184
                · linarith only [h179, h184, hc24, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h186 | h186
                  · linarith only [h179, h181, h186, h7, hc13, hlam, hphi, u1ehi3]
                  · rcases h1bigk with h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h181, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p188_1]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      rcases p188_3 (m.d 0 1) (by simp) with h191 | h191
                      · rcases p188_3 (m.d 1 2) (by simp) with h192 | h192
                        · linarith only [h0, h192, hlam]
                        · linarith only [h192, h7, hlam]
                      · linarith only [h191, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      rcases p188_3 (m.d 0 1) (by simp) with h196 | h196
                      · rcases p188_3 (m.d 1 2) (by simp) with h197 | h197
                        · linarith only [h0, h197, hlam]
                        · linarith only [h197, h8, hlam]
                      · linarith only [h196, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      rcases p188_3 (m.d 0 1) (by simp) with h201 | h201
                      · rcases p188_3 (m.d 1 2) (by simp) with h202 | h202
                        · linarith only [h0, h202, hlam]
                        · linarith only [h202, h9, hlam]
                      · linarith only [h201, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h0, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hc12, hlam, hphi, p188_1, u1ehi2]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p188_1, u1ehi3]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p188_1, u1ehi4]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h1, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h7, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h0, h11, h186, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p188_1, u1ehi3]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h11, hlam, p188_1]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h2, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h8, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h10, hlam, p188_1]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h179, hlam, p188_1]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h3, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h9, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hc15, hlam, hphi, p188_1, u1ehi2]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h0, h11, h186, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p188_1, u1ehi3]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hlam, p188_0]
            · linarith only [h10, h11, h181, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h227 | h227
        · rcases m.htr 1 4 5 (by decide) (by decide) with h228 | h228
          · rcases m.htr 2 3 4 (by decide) (by decide) with h229 | h229
            · linarith only [h10, h229, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h231 | h231
              · rcases m.htr 2 4 5 (by decide) (by decide) with h232 | h232
                · rcases m.htr 3 4 5 (by decide) (by decide) with h233 | h233
                  · rcases h1bigk with h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h231, h233, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p234_1]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      rcases p234_3 (m.d 0 1) (by simp) with h237 | h237
                      · rcases p234_3 (m.d 1 2) (by simp) with h238 | h238
                        · linarith only [h0, h238, hlam]
                        · linarith only [h238, h7, hlam]
                      · linarith only [h237, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      rcases p234_3 (m.d 0 1) (by simp) with h242 | h242
                      · rcases p234_3 (m.d 1 2) (by simp) with h243 | h243
                        · linarith only [h0, h243, hlam]
                        · linarith only [h243, h8, hlam]
                      · linarith only [h242, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      rcases p234_3 (m.d 0 1) (by simp) with h247 | h247
                      · rcases p234_3 (m.d 1 2) (by simp) with h248 | h248
                        · linarith only [h0, h248, hlam]
                        · linarith only [h248, h9, hlam]
                      · linarith only [h247, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h0, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h227, hc12, hlam, hphi, p234_1, u1ehi4]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h0, h10, h227, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p234_1, u1ehi4]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p234_1, u1ehi4]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h1, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h7, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h10, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [hc13, hlam, hphi, p234_1, u1ehi4]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h2, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h8, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [hc14, hlam, hphi, p234_1, u1ehi2]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h1, h10, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p234_1, u1ehi4]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h3, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h9, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h227, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h228, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [hlam, p234_0]
                  · linarith only [h10, h233, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                · linarith only [h2, h228, h229, h231, h232, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h1, h10, h227, h231, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h10, h227, h228, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h276 | h276
          · rcases m.htr 2 3 4 (by decide) (by decide) with h277 | h277
            · linarith only [h10, h277, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h279 | h279
              · linarith only [h227, h279, hc23, hlam, hphi, ht12, u1ehi2]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h281 | h281
                · rcases m.htr 3 4 5 (by decide) (by decide) with h282 | h282
                  · rcases h1bigk with h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h281, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p283_1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      rcases p283_3 (m.d 0 1) (by simp) with h286 | h286
                      · rcases p283_3 (m.d 1 2) (by simp) with h287 | h287
                        · linarith only [h0, h287, hlam]
                        · linarith only [h287, h7, hlam]
                      · linarith only [h286, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      rcases p283_3 (m.d 0 1) (by simp) with h291 | h291
                      · rcases p283_3 (m.d 1 2) (by simp) with h292 | h292
                        · linarith only [h0, h292, hlam]
                        · linarith only [h292, h8, hlam]
                      · linarith only [h291, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      rcases p283_3 (m.d 0 1) (by simp) with h296 | h296
                      · rcases p283_3 (m.d 1 2) (by simp) with h297 | h297
                        · linarith only [h0, h297, hlam]
                        · linarith only [h297, h9, hlam]
                      · linarith only [h296, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h0, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hc12, hlam, hphi, p283_1, u1ehi2]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h0, h227, h276, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p283_1, u1ehi2]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h0, h227, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p283_1, u1ehi2]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h1, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h7, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h10, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h227, hlam, p283_1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h2, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h8, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hc14, hlam, hphi, p283_1, u1ehi2]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h1, h10, h227, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p283_1, u1ehi2]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h3, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h9, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hc15, hlam, hphi, p283_1, u1ehi2]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h276, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hlam, p283_0]
                  · linarith only [h10, h281, h282, hc24, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h322 | h322
                  · rcases h1bigk with h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h276, h277, h281, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p323_1]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      rcases p323_3 (m.d 0 1) (by simp) with h326 | h326
                      · rcases p323_3 (m.d 1 2) (by simp) with h327 | h327
                        · linarith only [h0, h327, hlam]
                        · linarith only [h327, h7, hlam]
                      · linarith only [h326, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h276, h277, h281, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p323_1]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      rcases p323_3 (m.d 0 1) (by simp) with h332 | h332
                      · rcases p323_3 (m.d 1 2) (by simp) with h333 | h333
                        · linarith only [h0, h333, hlam]
                        · linarith only [h333, h9, hlam]
                      · linarith only [h332, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h0, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hc12, hlam, hphi, p323_1, u1ehi2]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h0, h276, h277, h281, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p323_1]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h0, h227, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p323_1, u1ehi2]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h1, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h7, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h10, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h227, hlam, p323_1]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h2, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h8, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hc14, hlam, hphi, p323_1, u1ehi2]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h1, h10, h227, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p323_1, u1ehi2]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h3, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h9, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hc15, hlam, hphi, p323_1, u1ehi2]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h276, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hlam, p323_0]
                  · linarith only [h0, h10, h322, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h358 | h358
            · linarith only [h10, h358, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h360 | h360
              · linarith only [h227, h360, hc23, hlam, hphi, ht12, u1ehi2]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h362 | h362
                · linarith only [h276, h362, h8, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h364 | h364
                  · linarith only [h276, h364, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                  · linarith only [h10, h364, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h367 | h367
      · rcases m.htr 1 3 5 (by decide) (by decide) with h368 | h368
        · linarith only [h368, h7, h9, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h370 | h370
          · linarith only [h370, h8, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h372 | h372
            · rcases m.htr 2 3 5 (by decide) (by decide) with h373 | h373
              · linarith only [h368, h373, h7, h9, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h375 | h375
                · linarith only [h370, h372, h373, h375, h7, h9, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                · linarith only [h0, h372, h375, h4, h6, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h367, h368, h372, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h379 | h379
        · linarith only [h379, h7, h9, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h381 | h381
          · linarith only [h381, h8, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h383 | h383
            · linarith only [h367, h383, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h385 | h385
              · linarith only [h379, h385, hc23, hlam, hphi, ht12, u1ehi2]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h387 | h387
                · linarith only [h367, h381, h385, h387, h8, h9, hc35, hlam, hphi, ht12, ht23, u1ehi2]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h389 | h389
                  · linarith only [h383, h387, h389, h8, h9, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h367, h389, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h392 | h392
    · rcases m.htr 1 3 4 (by decide) (by decide) with h393 | h393
      · linarith only [h393, h7, h8, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h395 | h395
        · rcases m.htr 1 4 5 (by decide) (by decide) with h396 | h396
          · rcases m.htr 2 3 4 (by decide) (by decide) with h397 | h397
            · linarith only [h393, h397, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h399 | h399
              · linarith only [h0, h399, h4, h7, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h1, h395, h397, h399, h5, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h395, h396, h7, h8, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h403 | h403
          · rcases m.htr 2 3 4 (by decide) (by decide) with h404 | h404
            · linarith only [h0, h4, h404, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h406 | h406
              · linarith only [h1, h395, h404, h406, h5, h7, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h408 | h408
                · rcases m.htr 3 4 5 (by decide) (by decide) with h409 | h409
                  · rcases h1bigk with h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [hlam, p410_0]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      rcases p410_3 (m.d 0 1) (by simp) with h412 | h412
                      · rcases p410_3 (m.d 1 2) (by simp) with h413 | h413
                        · linarith only [h413, hlam, p410_0]
                        · rcases p410_3 (m.d 1 3) (by simp) with h415 | h415
                          · linarith only [h1, h415, hlam]
                          · rcases p410_3 (m.d 1 4) (by simp) with h417 | h417
                            · linarith only [h2, h417, hlam]
                            · linarith only [h417, h8, hlam]
                      · linarith only [h412, hlam, p410_0]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      rcases p410_3 (m.d 0 1) (by simp) with h421 | h421
                      · rcases p410_3 (m.d 1 2) (by simp) with h422 | h422
                        · linarith only [h0, h422, hlam]
                        · linarith only [h422, h7, hlam]
                      · linarith only [h421, hlam, p410_0]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      rcases p410_3 (m.d 0 1) (by simp) with h426 | h426
                      · rcases p410_3 (m.d 1 2) (by simp) with h427 | h427
                        · linarith only [h0, h427, hlam]
                        · rcases p410_3 (m.d 1 3) (by simp) with h429 | h429
                          · linarith only [h1, h429, hlam]
                          · rcases p410_3 (m.d 1 4) (by simp) with h431 | h431
                            · linarith only [h431, hlam, p410_0]
                            · rcases p410_3 (m.d 1 5) (by simp) with h433 | h433
                              · linarith only [h3, h433, hlam]
                              · rcases h4bigk with h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  rcases p435_3 (m.d 0 4) (by simp) with h437 | h437
                                  · rcases p435_3 (m.d 1 4) (by simp) with h438 | h438
                                    · linarith only [h2, h438, hlam]
                                    · rcases p435_3 (m.d 2 4) (by simp) with h440 | h440
                                      · linarith only [h4, h440, hlam]
                                      · linarith only [h440, h8, hlam]
                                  · linarith only [h2, h437, hlam]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h0, h392, h4, h406, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h0, h393, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p435_1, u1ehi2]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  rcases p435_3 (m.d 0 4) (by simp) with h446 | h446
                                  · rcases p435_3 (m.d 1 4) (by simp) with h447 | h447
                                    · linarith only [h2, h447, hlam]
                                    · linarith only [h403, h447, hlam]
                                  · linarith only [h446, hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h2, hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h8, hlam, p435_1]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h393, hlam, p435_1]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p410_1, p435_1]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h4, hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h1, h404, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p435_1, u1ehi3]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h404, hlam, p435_1]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  rcases p435_3 (m.d 0 4) (by simp) with h460 | h460
                                  · rcases p435_3 (m.d 1 4) (by simp) with h461 | h461
                                    · linarith only [h461, h8, hlam]
                                    · linarith only [h403, h461, hlam]
                                  · linarith only [h460, h6, hlam]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h5, hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h1, h392, h5, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p435_1]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h1, h5, h7, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p435_1, u1ehi2]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  rcases p435_3 (m.d 0 4) (by simp) with h469 | h469
                                  · rcases p435_3 (m.d 1 4) (by simp) with h470 | h470
                                    · linarith only [h393, h470, hlam]
                                    · linarith only [h403, h470, hlam]
                                  · linarith only [h469, h6, hlam]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h6, hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h403, hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h408, hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [h409, hlam, p435_0]
                                · have p435_0 := h435c.1
                                  have p435_1 := h435c.2.1
                                  have p435_2 := h435c.2.2.1
                                  have p435_3 := h435c.2.2.2
                                  linarith only [hlam, p435_0]
                      · linarith only [h426, hlam, p410_0]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      rcases p410_3 (m.d 0 1) (by simp) with h480 | h480
                      · rcases p410_3 (m.d 1 2) (by simp) with h481 | h481
                        · linarith only [h0, h481, hlam]
                        · linarith only [h392, h481, hlam]
                      · linarith only [h480, hlam, p410_0]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [h0, hlam, p410_0]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [hlam, p410_0]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [hc12, hlam, hphi, p410_1, u1ehi2]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [h8, hlam, p410_1]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [h0, h395, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p410_1, u1ehi2]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [h1, hlam, p410_0]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [h7, hlam, p410_0]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [hlam, p410_0]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [h393, hlam, p410_0]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [h395, hlam, p410_1]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [h2, hlam, p410_0]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p410_1, u1ehi1]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p410_1, u1ehi2]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [hlam, p410_0]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [h0, h395, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p410_1, u1ehi2]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [h3, hlam, p410_0]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [h392, hlam, p410_0]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [h392, hc12, hlam, hphi, p410_1, u1ehi2]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [h403, hlam, p410_0]
                    · have p410_0 := h410c.1
                      have p410_1 := h410c.2.1
                      have p410_2 := h410c.2.2.1
                      have p410_3 := h410c.2.2.2
                      linarith only [hlam, p410_0]
                  · linarith only [h404, h409, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                · linarith only [h392, h403, h408, h8, hlam]
          · linarith only [h392, h403, h8, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h508 | h508
      · linarith only [h508, h7, h8, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h510 | h510
        · linarith only [h392, h510, h7, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h512 | h512
          · rcases m.htr 2 3 4 (by decide) (by decide) with h513 | h513
            · linarith only [h508, h513, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h515 | h515
              · linarith only [h1, h5, h510, h513, h515, h7, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h517 | h517
                · rcases m.htr 3 4 5 (by decide) (by decide) with h518 | h518
                  · rcases h1bigk with h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [hlam, p519_0]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      rcases p519_3 (m.d 0 1) (by simp) with h521 | h521
                      · rcases p519_3 (m.d 1 2) (by simp) with h522 | h522
                        · linarith only [h522, hlam, p519_0]
                        · rcases p519_3 (m.d 1 3) (by simp) with h524 | h524
                          · linarith only [h1, h524, hlam]
                          · rcases p519_3 (m.d 1 4) (by simp) with h526 | h526
                            · linarith only [h2, h526, hlam]
                            · linarith only [h526, h8, hlam]
                      · linarith only [h521, hlam, p519_0]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      rcases p519_3 (m.d 0 1) (by simp) with h530 | h530
                      · rcases p519_3 (m.d 1 2) (by simp) with h531 | h531
                        · linarith only [h0, h531, hlam]
                        · linarith only [h531, h7, hlam]
                      · linarith only [h530, hlam, p519_0]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      rcases p519_3 (m.d 0 1) (by simp) with h535 | h535
                      · rcases p519_3 (m.d 1 2) (by simp) with h536 | h536
                        · linarith only [h0, h536, hlam]
                        · rcases p519_3 (m.d 1 3) (by simp) with h538 | h538
                          · linarith only [h1, h538, hlam]
                          · rcases p519_3 (m.d 1 4) (by simp) with h540 | h540
                            · linarith only [h540, hlam, p519_0]
                            · rcases p519_3 (m.d 1 5) (by simp) with h542 | h542
                              · linarith only [h3, h542, hlam]
                              · rcases h4bigk with h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [hlam, p544_0]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  rcases p544_3 (m.d 0 4) (by simp) with h546 | h546
                                  · rcases p544_3 (m.d 1 4) (by simp) with h547 | h547
                                    · linarith only [h2, h547, hlam]
                                    · rcases p544_3 (m.d 2 4) (by simp) with h549 | h549
                                      · linarith only [h4, h549, hlam]
                                      · linarith only [h549, h8, hlam]
                                  · linarith only [h2, h546, hlam]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [h0, h4, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p544_1]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [h0, h4, h508, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p544_1, u1ehi2]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  rcases p544_3 (m.d 0 4) (by simp) with h555 | h555
                                  · rcases p544_3 (m.d 1 4) (by simp) with h556 | h556
                                    · linarith only [h2, h556, hlam]
                                    · linarith only [h512, h556, hlam]
                                  · linarith only [h555, hlam, p544_0]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [h2, hlam, p544_0]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [hlam, p544_0]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [h8, hlam, p544_1]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [h508, hlam, p544_1]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p519_1, p544_1]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [h4, hlam, p544_0]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [h513, hc34, hlam, hphi, ht12, ht23, p544_1, u1ehi3]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [hlam, p544_0]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [h513, hlam, p544_1]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  rcases p544_3 (m.d 0 4) (by simp) with h569 | h569
                                  · rcases p544_3 (m.d 1 4) (by simp) with h570 | h570
                                    · linarith only [h570, h8, hlam]
                                    · linarith only [h512, h570, hlam]
                                  · linarith only [h569, h6, hlam]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [h5, hlam, p544_0]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [h1, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p544_1, u1ehi3]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [h1, h392, h5, h517, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p544_1]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [hlam, p544_0]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  rcases p544_3 (m.d 0 4) (by simp) with h578 | h578
                                  · rcases p544_3 (m.d 1 4) (by simp) with h579 | h579
                                    · linarith only [h508, h579, hlam]
                                    · linarith only [h512, h579, hlam]
                                  · linarith only [h578, h6, hlam]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [h6, hlam, p544_0]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [h512, hlam, p544_0]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [h517, hlam, p544_0]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [h518, hlam, p544_0]
                                · have p544_0 := h544c.1
                                  have p544_1 := h544c.2.1
                                  have p544_2 := h544c.2.2.1
                                  have p544_3 := h544c.2.2.2
                                  linarith only [hlam, p544_0]
                      · linarith only [h535, hlam, p519_0]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      rcases p519_3 (m.d 0 1) (by simp) with h589 | h589
                      · rcases p519_3 (m.d 1 2) (by simp) with h590 | h590
                        · linarith only [h0, h590, hlam]
                        · rcases p519_3 (m.d 1 3) (by simp) with h592 | h592
                          · linarith only [h1, h592, hlam]
                          · rcases p519_3 (m.d 1 4) (by simp) with h594 | h594
                            · linarith only [h2, h594, hlam]
                            · linarith only [h512, h594, hlam]
                      · linarith only [h589, hlam, p519_0]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [h0, hlam, p519_0]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [hlam, p519_0]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [hc12, hlam, hphi, p519_1, u1ehi2]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [h8, hlam, p519_1]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [h392, hlam, p519_1]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [h1, hlam, p519_0]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [h7, hlam, p519_0]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [hlam, p519_0]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [h508, hlam, p519_0]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [h510, hlam, p519_1]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [h2, hlam, p519_0]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p519_1, u1ehi1]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p519_1, u1ehi2]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [hlam, p519_0]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p519_1, u1ehi4]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [h3, hlam, p519_0]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [h7, hc15, hlam, hphi, p519_1, u1ehi2]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p519_1, u1ehi2]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [h512, hlam, p519_0]
                    · have p519_0 := h519c.1
                      have p519_1 := h519c.2.1
                      have p519_2 := h519c.2.2.1
                      have p519_3 := h519c.2.2.2
                      linarith only [hlam, p519_0]
                  · linarith only [h0, h4, h513, h518, h6, h7, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                · linarith only [h512, h517, h7, h8, hc14, hlam, hphi, u1ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h620 | h620
            · linarith only [h508, h620, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h622 | h622
              · linarith only [h1, h5, h620, h622, h7, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h624 | h624
                · linarith only [h1, h5, h512, h620, h624, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h624, h7, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]

end R2N4
