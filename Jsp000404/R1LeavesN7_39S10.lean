import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_39S7
import Jsp000404.R1LeavesN7_39S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1769 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1894 | h1894
  · exact r1l7_11_23_L_I_M_IR_x1_x1_x0 m hb1 hb3 h0 h1769 h1894
  · exact r1l7_11_23_L_I_M_IR_x1_x1_x1 m hb1 hb3 h0 h1769 h1894

set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1769 | h1769
  · exact r1l7_11_23_L_I_M_IR_x1_x0 m hb1 hb3 h0 h1769
  · exact r1l7_11_23_L_I_M_IR_x1_x1 m hb1 hb3 h0 h1769

set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_23_L_I_M_IR_x0 m hb1 hb3 h0
  · exact r1l7_11_23_L_I_M_IR_x1 m hb1 hb3 h0

set_option maxHeartbeats 6948000 in
set_option maxHeartbeats 6948000 in
theorem r1l7_20_12_13_H_I_L_0_L_I_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
    · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
            · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
              · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                      · linarith only [h0, h10, h14, h16, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                      · rcases h0bigk with h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h13, h16, h2, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h13, h16, h2, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h13, h16, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h16, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h0, hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h13, h16, h2, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p18_1, u2elo0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h13, h16, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p18_1, u2elo0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p18_1, u2elo0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h1, hlam, p18_1]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h4, hlam, p18_1]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h13, h16, h2, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h3, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p18_1, u2elo0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h2, hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h5, hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h7, hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h3, h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p18_1, u2elo0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h3, hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h6, hlam, p18_1]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h8, hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h9, hlam, p18_1]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [hlam, p18_0]
                    · linarith only [h14, h15, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
                    · linarith only [h1, h11, h14, h4, h45, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
                      · rcases h0bigk with h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [hlam, p48_0]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h1, h11, h4, h45, h47, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h1, h11, h45, h47, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h45, h47, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h45, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h0, hlam, p48_0]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [hlam, p48_0]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h1, h11, h45, h47, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p48_1, u2elo0]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h45, h47, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p48_1, u2elo0]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p48_1, u2elo0]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h1, hlam, p48_1]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h4, hlam, p48_1]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [hlam, p48_0]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h45, h47, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h3, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p48_1, u2elo0]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h2, hlam, p48_0]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h5, hlam, p48_0]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h7, hlam, p48_0]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [hlam, p48_0]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h45, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h3, hlam, p48_0]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h6, hlam, p48_1]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h8, hlam, p48_0]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [h9, hlam, p48_1]
                        · have p48_0 := h48c.1
                          have p48_1 := h48c.2.1
                          have p48_2 := h48c.2.2.1
                          have p48_3 := h48c.2.2.2
                          linarith only [hlam, p48_0]
                      · linarith only [h1, h11, h13, h14, h4, h47, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h75 | h75
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h76 | h76
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                      · linarith only [h13, h75, h77, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · rcases h0bigk with h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p79_1]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h4, h76, hc01, hc35, hlam, hphi, ht0b, ht5b, p79_1]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h11, h13, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p79_1]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h11, h13, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p79_1]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h0, hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h11, h13, h8, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p79_1]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h11, h13, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p79_1, u2elo0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h11, h13, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p79_1, u2elo0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h1, hlam, p79_1]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h4, hlam, p79_1]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h11, h13, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p79_1]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h11, h13, h4, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p79_1, u2elo0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h2, hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h5, hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h7, hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h11, h13, h9, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p79_1]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h3, hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h6, hlam, p79_1]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h8, hlam, p79_0]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [h9, hlam, p79_1]
                        · have p79_0 := h79c.1
                          have p79_1 := h79c.2.1
                          have p79_2 := h79c.2.2.1
                          have p79_3 := h79c.2.2.2
                          linarith only [hlam, p79_0]
                    · linarith only [h4, h75, h76, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · linarith only [h11, h13, h4, h7, h75, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h11, h12, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h108 | h108
              · linarith only [h108, h11, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h110 | h110
                · rcases m.htr 2 3 4 (by decide) (by decide) with h111 | h111
                  · linarith only [h10, h11, h111, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h113 | h113
                    · linarith only [h10, h108, h113, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h115 | h115
                      · rcases h0bigk with h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h110, h2, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p116_1]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h110, h2, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p116_1]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h110, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p116_1]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h10, h108, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p116_1]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h0, hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h110, h2, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p116_1]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h110, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p116_1, u2elo0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h10, h108, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p116_1, u2elo0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h1, hlam, p116_1]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h4, hlam, p116_1]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h110, h2, hc03, hc45, hlam, hphi, ht0b, ht5b, p116_1]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h10, h108, h4, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p116_1, u2elo0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h2, hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h5, hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h7, hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h10, h108, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p116_1]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h3, hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h6, hlam, p116_1]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h8, hlam, p116_0]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [h9, hlam, p116_1]
                        · have p116_0 := h116c.1
                          have p116_1 := h116c.2.1
                          have p116_2 := h116c.2.2.1
                          have p116_3 := h116c.2.2.2
                          linarith only [hlam, p116_0]
                      · linarith only [h10, h11, h110, h115, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h143 | h143
                  · linarith only [h10, h108, h143, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h145 | h145
                    · linarith only [h10, h108, h145, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h147 | h147
                      · linarith only [h10, h11, h110, h147, h4, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h10, h11, h147, h4, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h10, h4, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h151 | h151
          · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
            · rcases m.htr 1 3 5 (by decide) (by decide) with h153 | h153
              · rcases m.htr 1 4 5 (by decide) (by decide) with h154 | h154
                · linarith only [h154, h2, h9, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h156 | h156
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h157 | h157
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h158 | h158
                      · linarith only [h158, h4, h7, h9, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases h0bigk with h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [hlam, p160_0]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h0, h151, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p160_1]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h157, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p160_1]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          rcases p160_3 (m.d 0 1) (by simp) with h164 | h164
                          · rcases p160_3 (m.d 0 2) (by simp) with h165 | h165
                            · linarith only [h0, h165, hlam]
                            · linarith only [h165, h5, hlam]
                          · linarith only [h164, h2, hlam]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          rcases p160_3 (m.d 0 1) (by simp) with h169 | h169
                          · rcases p160_3 (m.d 0 2) (by simp) with h170 | h170
                            · linarith only [h0, h170, hlam]
                            · linarith only [h170, h6, hlam]
                          · linarith only [h169, h3, hlam]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h0, hlam, p160_0]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [hlam, p160_0]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h1, h151, h157, h158, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p160_1, u2elo0]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h152, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p160_1, u2elo0]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h152, h2, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p160_1, u2elo0]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h1, hlam, p160_1]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h4, hlam, p160_1]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [hlam, p160_0]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h152, h2, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p160_1, u2elo0]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h152, h2, h4, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p160_1, u2elo0]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h2, hlam, p160_0]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h5, hlam, p160_0]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h7, hlam, p160_0]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [hlam, p160_0]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h9, hlam, p160_0]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h3, hlam, p160_0]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h6, hlam, p160_1]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h8, hlam, p160_0]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [h152, h2, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p160_1, u2elo0]
                        · have p160_0 := h160c.1
                          have p160_1 := h160c.2.1
                          have p160_2 := h160c.2.2.1
                          have p160_3 := h160c.2.2.2
                          linarith only [hlam, p160_0]
                    · linarith only [h1, h153, h156, h157, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h195 | h195
                    · linarith only [h156, h195, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h197 | h197
                      · linarith only [h152, h197, h2, h9, hlam]
                      · rcases h0bigk with h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [hlam, p199_0]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h1, h153, h156, h197, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h1, h153, h156, h197, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h152, h156, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h152, h154, h156, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h0, hlam, p199_0]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [hlam, p199_0]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h1, h153, h156, h197, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p199_1, u2elo0]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h152, h156, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p199_1, u2elo0]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h152, h154, h156, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p199_1, u2elo0]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h1, hlam, p199_1]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h4, hlam, p199_1]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [hlam, p199_0]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h152, h156, h2, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h152, h154, h156, h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p199_1, u2elo0]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h2, hlam, p199_0]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h5, hlam, p199_0]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h7, hlam, p199_0]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [hlam, p199_0]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h9, hlam, p199_0]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h3, hlam, p199_0]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h6, hlam, p199_1]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h8, hlam, p199_0]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [h152, h156, h2, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1]
                        · have p199_0 := h199c.1
                          have p199_1 := h199c.2.1
                          have p199_2 := h199c.2.2.1
                          have p199_3 := h199c.2.2.2
                          linarith only [hlam, p199_0]
              · linarith only [h152, h153, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h226 | h226
              · linarith only [h152, h226, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h228 | h228
                · linarith only [h2, h228, h9, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h230 | h230
                  · linarith only [h151, h152, h230, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h232 | h232
                    · linarith only [h151, h152, h226, h232, h4, h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h234 | h234
                      · linarith only [h234, h7, h9, hlam]
                      · rcases h0bigk with h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [hlam, p236_0]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h151, h152, h234, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p236_1]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h151, h152, h234, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p236_1]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h151, h152, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p236_1]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h151, h152, h234, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p236_1]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h0, hlam, p236_0]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [hlam, p236_0]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h151, h152, h234, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p236_1, u2elo0]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h151, h152, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p236_1, u2elo0]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p236_1, u2elo0]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h1, hlam, p236_1]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h4, hlam, p236_1]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [hlam, p236_0]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h151, h152, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p236_1]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h151, h152, h228, h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p236_1, u2elo0]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h2, hlam, p236_0]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h5, hlam, p236_0]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h7, hlam, p236_0]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [hlam, p236_0]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h9, hlam, p236_0]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h3, hlam, p236_0]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h6, hlam, p236_1]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h8, hlam, p236_0]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [h151, h152, h7, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p236_1]
                        · have p236_0 := h236c.1
                          have p236_1 := h236c.2.1
                          have p236_2 := h236c.2.2.1
                          have p236_3 := h236c.2.2.2
                          linarith only [hlam, p236_0]
          · linarith only [h151, h4, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h263 | h263
        · linarith only [h263, h7, h8, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h265 | h265
          · rcases m.htr 1 3 4 (by decide) (by decide) with h266 | h266
            · rcases m.htr 1 3 5 (by decide) (by decide) with h267 | h267
              · linarith only [h1, h267, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h269 | h269
                · linarith only [h2, h263, h269, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h271 | h271
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h272 | h272
                    · linarith only [h1, h265, h272, h8, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h274 | h274
                      · linarith only [h0, h263, h265, h271, h274, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h0bigk with h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h0, h265, h271, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p276_1]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h1, h265, h271, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p276_1]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          rcases p276_3 (m.d 0 1) (by simp) with h280 | h280
                          · rcases p276_3 (m.d 0 2) (by simp) with h281 | h281
                            · linarith only [h0, h281, hlam]
                            · linarith only [h281, h5, hlam]
                          · linarith only [h2, h280, hlam]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h1, h265, h271, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p276_1]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h0, hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h1, h265, h271, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p276_1]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h271, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p276_1, u2elo0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h1, h265, h271, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p276_1, u2elo0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h1, hlam, p276_1]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h4, hlam, p276_1]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h271, h5, h8, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p276_1]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h8, hlam, p276_1]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h2, hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h5, hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h7, hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h263, hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h3, hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h6, hlam, p276_1]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h1, h265, h271, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p276_1]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h271, h5, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p276_1, u2elo0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [hlam, p276_0]
                  · linarith only [h271, h7, h8, hc23, hc35, hlam, hphi]
            · linarith only [h265, h266, h7, h8, hc23, hc35, hlam, hphi]
          · linarith only [h265, h4, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h309 | h309
      · rcases m.htr 0 4 5 (by decide) (by decide) with h310 | h310
        · rcases m.htr 1 2 3 (by decide) (by decide) with h311 | h311
          · rcases m.htr 1 3 4 (by decide) (by decide) with h312 | h312
            · linarith only [h1, h309, h312, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h314 | h314
              · rcases m.htr 1 4 5 (by decide) (by decide) with h315 | h315
                · rcases m.htr 2 3 4 (by decide) (by decide) with h316 | h316
                  · linarith only [h1, h311, h314, h316, h7, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h318 | h318
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h319 | h319
                      · rcases h0bigk with h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [hlam, p320_0]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h318, h319, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p320_1]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h1, h311, h318, h319, hc01, hc45, hlam, hphi, ht0b, ht5b, p320_1]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h316, h318, h319, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p320_1]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          rcases p320_3 (m.d 0 1) (by simp) with h325 | h325
                          · rcases p320_3 (m.d 0 2) (by simp) with h326 | h326
                            · linarith only [h0, h326, hlam]
                            · linarith only [h326, h6, hlam]
                          · linarith only [h3, h325, hlam]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h0, hlam, p320_0]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [hlam, p320_0]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h1, h311, h318, h319, hc02, hc45, hlam, hphi, ht0b, ht5b, p320_1]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h1, h311, h318, h319, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p320_1, u2elo0]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p320_1, u2elo0]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h1, hlam, p320_1]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h4, hlam, p320_1]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [hlam, p320_0]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h7, hlam, p320_1]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h6, h7, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p320_1]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h2, hlam, p320_0]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h5, hlam, p320_0]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h1, h311, h318, h319, hc04, hc45, hlam, hphi, ht0b, ht5b, p320_1]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [hlam, p320_0]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h309, h319, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p320_1, u2elo0]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h3, hlam, p320_0]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h6, hlam, p320_1]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h309, hlam, p320_0]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [h310, hlam, p320_1]
                        · have p320_0 := h320c.1
                          have p320_1 := h320c.2.1
                          have p320_2 := h320c.2.2.1
                          have p320_3 := h320c.2.2.2
                          linarith only [hlam, p320_0]
                      · linarith only [h1, h3, h311, h315, h318, h319, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1, h314, h318, h7, hc23, hc34, hlam, hphi]
                · linarith only [h310, h312, h314, h315, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
              · linarith only [h309, h311, h314, h7, hc23, hc34, hlam, hphi]
          · linarith only [h311, h4, hc12, hlam, hphi, u2elo0]
        · linarith only [h309, h310, h7, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h356 | h356
        · rcases m.htr 1 2 3 (by decide) (by decide) with h357 | h357
          · rcases m.htr 1 3 4 (by decide) (by decide) with h358 | h358
            · linarith only [h1, h358, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h360 | h360
              · linarith only [h1, h309, h360, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h362 | h362
                · rcases m.htr 2 3 4 (by decide) (by decide) with h363 | h363
                  · linarith only [h357, h363, h7, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h365 | h365
                    · linarith only [h1, h309, h357, h365, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h367 | h367
                      · rcases h0bigk with h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [hlam, p368_0]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p368_1]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          rcases p368_3 (m.d 0 1) (by simp) with h371 | h371
                          · rcases p368_3 (m.d 0 2) (by simp) with h372 | h372
                            · linarith only [h0, h372, hlam]
                            · linarith only [h372, h4, hlam]
                          · linarith only [h1, h371, hlam]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [h2, h362, hc01, hc45, hlam, hphi, ht0b, ht5b, p368_1]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          rcases p368_3 (m.d 0 1) (by simp) with h377 | h377
                          · rcases p368_3 (m.d 0 2) (by simp) with h378 | h378
                            · linarith only [h0, h378, hlam]
                            · linarith only [h378, h6, hlam]
                          · linarith only [h3, h377, hlam]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [h0, hlam, p368_0]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [hlam, p368_0]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [h1, h357, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p368_1, u2elo0]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [h2, h362, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p368_1, u2elo0]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p368_1, u2elo0]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [h1, hlam, p368_1]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [h4, hlam, p368_1]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [hlam, p368_0]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [h7, hlam, p368_1]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [h309, hlam, p368_1]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [h2, hlam, p368_0]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [h5, hlam, p368_0]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [h1, h357, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p368_1, u2elo0]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [hlam, p368_0]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [h1, h309, h357, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p368_1, u2elo0]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [h3, hlam, p368_0]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [h6, hlam, p368_1]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [h1, h357, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p368_1, u2elo0]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [h356, hlam, p368_1]
                        · have p368_0 := h368c.1
                          have p368_1 := h368c.2.1
                          have p368_2 := h368c.2.2.1
                          have p368_3 := h368c.2.2.2
                          linarith only [hlam, p368_0]
                      · linarith only [h2, h362, h367, h7, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h403 | h403
                  · linarith only [h356, h357, h358, h362, h403, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h405 | h405
                    · linarith only [h3, h309, h357, h358, h362, h405, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h407 | h407
                      · rcases h0bigk with h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [hlam, p408_0]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p408_1]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          rcases p408_3 (m.d 0 1) (by simp) with h411 | h411
                          · rcases p408_3 (m.d 0 2) (by simp) with h412 | h412
                            · linarith only [h0, h412, hlam]
                            · linarith only [h4, h412, hlam]
                          · linarith only [h1, h411, hlam]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h356, h357, h358, h362, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p408_1]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h356, h357, h358, h362, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p408_1]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h0, hlam, p408_0]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [hlam, p408_0]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h1, h357, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p408_1, u2elo0]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h356, h357, h358, h362, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p408_1, u2elo0]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h356, h357, h358, h362, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p408_1, u2elo0]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h1, hlam, p408_1]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h4, hlam, p408_1]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [hlam, p408_0]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h7, hlam, p408_1]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h309, hlam, p408_1]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h2, hlam, p408_0]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h5, hlam, p408_0]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h1, h357, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p408_1, u2elo0]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [hlam, p408_0]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h356, h357, h358, h362, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p408_1, u2elo0]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h3, hlam, p408_0]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h6, hlam, p408_1]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h1, h309, h357, hc23, hc35, hlam, hphi, p408_1]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [h356, hlam, p408_1]
                        · have p408_0 := h408c.1
                          have p408_1 := h408c.2.1
                          have p408_2 := h408c.2.2.1
                          have p408_3 := h408c.2.2.2
                          linarith only [hlam, p408_0]
                      · linarith only [h356, h407, h7, hlam]
          · linarith only [h357, h4, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h440 | h440
          · rcases m.htr 1 3 4 (by decide) (by decide) with h441 | h441
            · linarith only [h1, h441, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h443 | h443
              · linarith only [h1, h309, h443, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h445 | h445
                · linarith only [h2, h356, h445, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h447 | h447
                  · linarith only [h1, h440, h447, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h449 | h449
                    · linarith only [h1, h309, h440, h449, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h451 | h451
                      · rcases h0bigk with h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [hlam, p452_0]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p452_1]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          rcases p452_3 (m.d 0 1) (by simp) with h455 | h455
                          · rcases p452_3 (m.d 0 2) (by simp) with h456 | h456
                            · linarith only [h0, h456, hlam]
                            · linarith only [h4, h456, hlam]
                          · linarith only [h1, h455, hlam]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          rcases p452_3 (m.d 0 1) (by simp) with h460 | h460
                          · rcases p452_3 (m.d 0 2) (by simp) with h461 | h461
                            · linarith only [h0, h461, hlam]
                            · linarith only [h461, h5, hlam]
                          · linarith only [h2, h460, hlam]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          rcases p452_3 (m.d 0 1) (by simp) with h465 | h465
                          · rcases p452_3 (m.d 0 2) (by simp) with h466 | h466
                            · linarith only [h0, h466, hlam]
                            · linarith only [h466, h6, hlam]
                          · linarith only [h3, h465, hlam]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [h0, hlam, p452_0]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [hlam, p452_0]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p452_1, u2elo0]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [h1, h7, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p452_1, u2elo0]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [h1, h356, h7, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p452_1, u2elo0]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [h1, hlam, p452_1]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [h4, hlam, p452_1]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [hlam, p452_0]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [h7, hlam, p452_1]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [h309, hlam, p452_1]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [h2, hlam, p452_0]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [h5, hlam, p452_0]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [h1, h356, h451, hc13, hc34, hlam, hphi, p452_1]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [hlam, p452_0]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [h356, hlam, p452_0]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [h3, hlam, p452_0]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [h6, hlam, p452_1]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [h1, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p452_1, u2elo0]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [h356, h451, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p452_1]
                        · have p452_0 := h452c.1
                          have p452_1 := h452c.2.1
                          have p452_2 := h452c.2.2.1
                          have p452_3 := h452c.2.2.2
                          linarith only [hlam, p452_0]
                      · rcases h0bigk with h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [hlam, p490_0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p490_1]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          rcases p490_3 (m.d 0 1) (by simp) with h493 | h493
                          · rcases p490_3 (m.d 0 2) (by simp) with h494 | h494
                            · linarith only [h0, h494, hlam]
                            · linarith only [h4, h494, hlam]
                          · linarith only [h1, h493, hlam]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          rcases p490_3 (m.d 0 1) (by simp) with h498 | h498
                          · rcases p490_3 (m.d 0 2) (by simp) with h499 | h499
                            · linarith only [h0, h499, hlam]
                            · linarith only [h499, h5, hlam]
                          · linarith only [h2, h498, hlam]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          rcases p490_3 (m.d 0 1) (by simp) with h503 | h503
                          · rcases p490_3 (m.d 0 2) (by simp) with h504 | h504
                            · linarith only [h0, h504, hlam]
                            · linarith only [h504, h6, hlam]
                          · linarith only [h3, h503, hlam]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h0, hlam, p490_0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [hlam, p490_0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p490_1, u2elo0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h1, h7, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p490_1, u2elo0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h1, h356, h7, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p490_1, u2elo0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h1, hlam, p490_1]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h4, hlam, p490_1]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [hlam, p490_0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h7, hlam, p490_1]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h309, hlam, p490_1]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h2, hlam, p490_0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h5, hlam, p490_0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h1, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p490_1, u2elo0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [hlam, p490_0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h356, hlam, p490_0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h3, hlam, p490_0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h6, hlam, p490_1]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h1, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p490_1, u2elo0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h6, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p490_1, u2elo0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [hlam, p490_0]
          · linarith only [h4, h440, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h529 | h529
    · rcases m.htr 0 3 5 (by decide) (by decide) with h530 | h530
      · linarith only [h4, h530, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h532 | h532
        · linarith only [h5, h532, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h534 | h534
          · rcases m.htr 1 3 4 (by decide) (by decide) with h535 | h535
            · rcases m.htr 1 3 5 (by decide) (by decide) with h536 | h536
              · linarith only [h1, h530, h536, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h538 | h538
                · linarith only [h2, h532, h538, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h540 | h540
                  · linarith only [h0, h534, h540, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · linarith only [h1, h530, h535, h540, hc23, hc35, hlam, hphi]
            · linarith only [h4, h529, h535, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
          · linarith only [h4, h534, h6, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h545 | h545
      · linarith only [h4, h545, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h547 | h547
        · linarith only [h5, h547, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h549 | h549
          · rcases m.htr 1 3 4 (by decide) (by decide) with h550 | h550
            · linarith only [h1, h529, h550, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h552 | h552
              · linarith only [h1, h545, h552, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h554 | h554
                · linarith only [h2, h547, h554, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h556 | h556
                  · linarith only [h1, h529, h549, h556, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h558 | h558
                    · linarith only [h545, h549, h558, h6, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h560 | h560
                      · rcases h0bigk with h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [hlam, p561_0]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h0, h549, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p561_1]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          rcases p561_3 (m.d 0 1) (by simp) with h564 | h564
                          · rcases p561_3 (m.d 0 2) (by simp) with h565 | h565
                            · linarith only [h0, h565, hlam]
                            · linarith only [h4, h565, hlam]
                          · linarith only [h1, h564, hlam]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          rcases p561_3 (m.d 0 1) (by simp) with h569 | h569
                          · rcases p561_3 (m.d 0 2) (by simp) with h570 | h570
                            · linarith only [h0, h570, hlam]
                            · linarith only [h5, h570, hlam]
                          · linarith only [h2, h569, hlam]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h0, h549, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p561_1]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h0, hlam, p561_0]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [hlam, p561_0]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h1, h549, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p561_1, u2elo4]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h6, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p561_1, u2elo4]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h6, hlam, p561_0]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h1, hlam, p561_1]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h4, hlam, p561_1]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [hlam, p561_0]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h529, hlam, p561_1]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h545, hlam, p561_1]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h2, hlam, p561_0]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h5, hlam, p561_0]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h1, h5, h549, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p561_1, u2elo4]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [hlam, p561_0]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h547, hlam, p561_0]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h3, hlam, p561_0]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h5, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p561_1]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h1, h549, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p561_1, u2elo4]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [h547, h560, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p561_1]
                        · have p561_0 := h561c.1
                          have p561_1 := h561c.2.1
                          have p561_2 := h561c.2.2.1
                          have p561_3 := h561c.2.2.2
                          linarith only [hlam, p561_0]
                      · rcases h0bigk with h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [hlam, p595_0]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h0, h549, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p595_1]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          rcases p595_3 (m.d 0 1) (by simp) with h598 | h598
                          · rcases p595_3 (m.d 0 2) (by simp) with h599 | h599
                            · linarith only [h0, h599, hlam]
                            · linarith only [h4, h599, hlam]
                          · linarith only [h1, h598, hlam]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          rcases p595_3 (m.d 0 1) (by simp) with h603 | h603
                          · rcases p595_3 (m.d 0 2) (by simp) with h604 | h604
                            · linarith only [h0, h604, hlam]
                            · linarith only [h5, h604, hlam]
                          · linarith only [h2, h603, hlam]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h0, h549, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p595_1]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h0, hlam, p595_0]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [hlam, p595_0]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h6, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p595_1, u2elo4]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h1, h529, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p595_1, u2elo4]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h6, hlam, p595_0]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h1, hlam, p595_1]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h4, hlam, p595_1]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [hlam, p595_0]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h529, hlam, p595_1]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h545, hlam, p595_1]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h2, hlam, p595_0]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h5, hlam, p595_0]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h1, h5, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p595_1, u2elo4]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [hlam, p595_0]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h547, hlam, p595_0]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h3, hlam, p595_0]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p595_1]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h1, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p595_1, u2elo4]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [h6, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p595_1, u2elo4]
                        · have p595_0 := h595c.1
                          have p595_1 := h595c.2.1
                          have p595_2 := h595c.2.2.1
                          have p595_3 := h595c.2.2.2
                          linarith only [hlam, p595_0]
          · linarith only [h4, h549, hc12, hlam, hphi, u2elo0]

end R2N4
