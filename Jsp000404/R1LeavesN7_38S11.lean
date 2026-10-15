import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_38S8
import Jsp000404.R1LeavesN7_38S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7284000 in
set_option maxHeartbeats 7284000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x1 m hb0 hb1 hb3 hb4 h0

set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
        · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                      · linarith only [h0, h10, h15, h18, hc01, hc45, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h10, h15, h17, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                      · linarith only [h17, h21, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                      · rcases h0bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p23_1]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h16, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p23_1]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h15, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h15, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h0, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h15, h17, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h0, h15, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h0, h15, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h1, hlam, p23_1]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h4, hlam, p23_1]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h15, h17, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p23_1, u3elo0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p23_1, u3elo0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h2, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h5, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h7, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h3, h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p23_1, u3elo0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h3, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h6, hlam, p23_1]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h8, hlam, p23_0]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [h9, hlam, p23_1]
                        · have p23_0 := h23c.1
                          have p23_1 := h23c.2.1
                          have p23_2 := h23c.2.2.1
                          have p23_3 := h23c.2.2.2
                          linarith only [hlam, p23_0]
                  · linarith only [h15, h16, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                · linarith only [h15, h7, hc23, hlam, hphi, u3elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                    · linarith only [h11, h14, h53, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h55 | h55
                      · linarith only [h11, h14, h51, h55, hlam]
                      · rcases h0bigk with h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [hlam, p57_0]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h4, h52, h55, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p57_1]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h4, h52, h55, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p57_1]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h11, h14, h51, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p57_1]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h11, h14, h51, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p57_1]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h0, hlam, p57_0]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [hlam, p57_0]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h11, h14, h51, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p57_1]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h0, h11, h14, h51, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p57_1]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h0, h11, h14, h51, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p57_1]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h1, hlam, p57_1]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h4, hlam, p57_1]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [hlam, p57_0]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h11, h14, h51, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p57_1]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p57_1, u3elo0]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h2, hlam, p57_0]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h5, hlam, p57_0]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h7, hlam, p57_0]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [hlam, p57_0]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h51, h53, h6, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p57_1, u3elo0]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h3, hlam, p57_0]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h6, hlam, p57_1]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h8, hlam, p57_0]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [h9, hlam, p57_1]
                        · have p57_0 := h57c.1
                          have p57_1 := h57c.2.1
                          have p57_2 := h57c.2.2.1
                          have p57_3 := h57c.2.2.2
                          linarith only [hlam, p57_0]
                  · linarith only [h52, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h51, h7, hc23, hlam, hphi, u3elo0]
            · linarith only [h13, h8, hc13, hlam, hphi, u3elo0]
          · linarith only [h10, h12, h6, h8, hc23, hlam, hphi, u3elo0]
        · linarith only [h10, h11, h5, h7, hc23, hlam, hphi, u3elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
        · rcases m.htr 1 2 5 (by decide) (by decide) with h89 | h89
          · rcases m.htr 1 3 5 (by decide) (by decide) with h90 | h90
            · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
              · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                · rcases m.htr 2 3 5 (by decide) (by decide) with h93 | h93
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h94 | h94
                    · linarith only [h10, h88, h94, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h10, h4, h88, h91, h94, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                  · linarith only [h10, h93, hc12, hlam, hphi, ht23, u3elo4]
                · linarith only [h10, h92, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h99 | h99
                · rcases m.htr 2 3 5 (by decide) (by decide) with h100 | h100
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h101 | h101
                    · linarith only [h10, h101, h88, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h103 | h103
                      · linarith only [h103, h7, h91, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                      · rcases h0bigk with h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h10, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p105_1]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p105_1]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h88, h9, h91, h99, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p105_1]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h88, h9, h91, h99, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p105_1]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h0, hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h7, h88, h9, h91, h99, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p105_1]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h0, h88, h9, h91, h99, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p105_1]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h0, h88, h9, h91, h99, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p105_1]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h1, hlam, p105_1]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h4, hlam, p105_1]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h88, h9, h91, h99, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p105_1, u3elo0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p105_1, u3elo0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h2, hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h5, hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h7, hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h3, h7, h89, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p105_1, u3elo0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h3, hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h6, hlam, p105_1]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h8, hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h9, hlam, p105_1]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [hlam, p105_0]
                  · linarith only [h10, h100, h88, h99, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · linarith only [h10, h99, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h10, h8, h88, h90, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h134 | h134
            · rcases m.htr 1 4 5 (by decide) (by decide) with h135 | h135
              · linarith only [h135, h88, h89, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h137 | h137
                · rcases m.htr 2 3 5 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h139 | h139
                    · linarith only [h135, h139, h6, h88, h89, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h139, h7, h89, h9, hc12, hlam, hphi, ht23, u3elo0]
                  · linarith only [h10, h134, h135, h138, h7, h9, hc13, hlam, hphi, u3elo0]
                · linarith only [h10, h137, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h10, h134, h8, h88, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h145 | h145
          · rcases m.htr 1 3 5 (by decide) (by decide) with h146 | h146
            · rcases m.htr 1 4 5 (by decide) (by decide) with h147 | h147
              · rcases m.htr 2 3 4 (by decide) (by decide) with h148 | h148
                · rcases m.htr 2 3 5 (by decide) (by decide) with h149 | h149
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h150 | h150
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h151 | h151
                      · rcases h0bigk with h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h0, h145, h149, h151, hc01, hc45, hlam, hphi, ht0b, ht5b, p152_1]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h1, h10, h145, h149, h151, hc01, hc45, hlam, hphi, ht0b, ht5b, p152_1]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h145, h149, h151, h2, h88, hc01, hc45, hlam, hphi, ht0b, ht5b, p152_1]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          rcases p152_3 (m.d 0 1) (by simp) with h157 | h157
                          · rcases p152_3 (m.d 0 2) (by simp) with h158 | h158
                            · linarith only [h0, h158, hlam]
                            · linarith only [h158, h6, hlam]
                          · linarith only [h157, h3, hlam]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h0, hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h145, h148, h149, h151, h4, h88, hc02, hc45, hlam, hphi, ht0b, ht5b, p152_1]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h0, h145, h149, h151, h5, h88, hc01, hc45, hlam, hphi, ht0b, ht5b, p152_1]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          rcases p152_3 (m.d 0 1) (by simp) with h166 | h166
                          · rcases p152_3 (m.d 0 2) (by simp) with h167 | h167
                            · rcases p152_3 (m.d 0 3) (by simp) with h168 | h168
                              · linarith only [h168, h4, hlam]
                              · linarith only [h168, h8, hlam]
                            · linarith only [h167, h6, hlam]
                          · linarith only [h166, h3, hlam]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h1, hlam, p152_1]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h4, hlam, p152_1]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h145, h149, h151, h5, h88, hc03, hc45, hlam, hphi, ht0b, ht5b, p152_1]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p152_1, u3elo0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h2, hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h5, hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h7, hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h149, h151, h6, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p152_1, u3elo0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h3, hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h6, hlam, p152_1]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h8, hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h9, hlam, p152_1]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [hlam, p152_0]
                      · linarith only [h145, h148, h150, h151, h4, h88, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                    · linarith only [h145, h147, h150, h88, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h145, h148, h149, h88, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                · linarith only [h148, h7, hc23, hlam, hphi, u3elo0]
              · linarith only [h145, h147, h7, h88, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
            · linarith only [h10, h145, h146, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h194 | h194
            · rcases m.htr 1 4 5 (by decide) (by decide) with h195 | h195
              · rcases m.htr 2 3 4 (by decide) (by decide) with h196 | h196
                · rcases m.htr 2 3 5 (by decide) (by decide) with h197 | h197
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h198 | h198
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h199 | h199
                      · rcases h0bigk with h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [hlam, p200_0]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h145, h196, h198, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p200_1]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h1, h194, hc01, hc35, hlam, hphi, ht0b, ht5b, p200_1]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h145, h198, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p200_1]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h145, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p200_1]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h0, hlam, p200_0]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [hlam, p200_0]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h145, h196, h198, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p200_1]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h0, h145, h198, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p200_1]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h0, h145, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p200_1]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h1, hlam, p200_1]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h4, hlam, p200_1]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [hlam, p200_0]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h145, h198, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p200_1]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h145, h6, hc12, hlam, hphi, ht23, p200_1, u3elo0]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h2, hlam, p200_0]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h5, hlam, p200_0]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h7, hlam, p200_0]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [hlam, p200_0]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h145, h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p200_1]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h3, hlam, p200_0]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h6, hlam, p200_1]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h8, hlam, p200_0]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [h9, hlam, p200_1]
                        · have p200_0 := h200c.1
                          have p200_1 := h200c.2.1
                          have p200_2 := h200c.2.2.1
                          have p200_3 := h200c.2.2.2
                          linarith only [hlam, p200_0]
                      · rcases h0bigk with h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [hlam, p226_0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h195, h196, h199, h4, h88, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h195, h196, h199, h4, h88, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h195, h199, h5, h88, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h145, h195, h196, h199, h4, h6, h88, hc01, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p226_1, u3elo0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h0, hlam, p226_0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [hlam, p226_0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h195, h196, h199, h4, h88, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h0, h195, h199, h5, h88, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h0, h145, h195, h196, h199, h4, h6, h88, hc01, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p226_1, u3elo0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h1, hlam, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h4, hlam, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [hlam, p226_0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h195, h199, h5, h88, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p226_1, u3elo0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h145, h6, hc12, hlam, hphi, ht23, p226_1, u3elo0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h2, hlam, p226_0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h5, hlam, p226_0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h7, hlam, p226_0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [hlam, p226_0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h145, h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h3, hlam, p226_0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h6, hlam, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h8, hlam, p226_0]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [h9, hlam, p226_1]
                        · have p226_0 := h226c.1
                          have p226_1 := h226c.2.1
                          have p226_2 := h226c.2.2.1
                          have p226_3 := h226c.2.2.2
                          linarith only [hlam, p226_0]
                    · linarith only [h195, h198, h88, hlam]
                  · linarith only [h197, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h10, h196, h7, hc13, hlam, hphi, u3elo0]
              · linarith only [h195, h7, h88, h9, hc12, hlam, hphi, ht23, u3elo0]
            · linarith only [h194, h8, hc13, hlam, hphi, u3elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h257 | h257
      · rcases m.htr 1 2 4 (by decide) (by decide) with h258 | h258
        · rcases m.htr 1 2 5 (by decide) (by decide) with h259 | h259
          · rcases m.htr 1 3 5 (by decide) (by decide) with h260 | h260
            · rcases m.htr 1 4 5 (by decide) (by decide) with h261 | h261
              · linarith only [h2, h261, h9, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h263 | h263
                · rcases m.htr 2 3 5 (by decide) (by decide) with h264 | h264
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h265 | h265
                    · linarith only [h2, h258, h265, h9, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h267 | h267
                      · linarith only [h2, h258, h263, h267, h9, hlam]
                      · rcases h0bigk with h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h0, h257, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p269_1]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h264, h267, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p269_1]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          rcases p269_3 (m.d 0 1) (by simp) with h273 | h273
                          · rcases p269_3 (m.d 0 2) (by simp) with h274 | h274
                            · linarith only [h0, h274, hlam]
                            · linarith only [h274, h5, hlam]
                          · linarith only [h2, h273, hlam]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          rcases p269_3 (m.d 0 1) (by simp) with h278 | h278
                          · rcases p269_3 (m.d 0 2) (by simp) with h279 | h279
                            · linarith only [h0, h279, hlam]
                            · linarith only [h279, h6, hlam]
                          · linarith only [h278, h3, hlam]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h0, hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h1, h257, h264, h267, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p269_1]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          rcases p269_3 (m.d 0 1) (by simp) with h286 | h286
                          · rcases p269_3 (m.d 0 2) (by simp) with h287 | h287
                            · rcases p269_3 (m.d 0 3) (by simp) with h288 | h288
                              · linarith only [h288, h4, hlam]
                              · linarith only [h288, h7, hlam]
                            · linarith only [h287, h5, hlam]
                          · linarith only [h2, h286, hlam]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          rcases p269_3 (m.d 0 1) (by simp) with h293 | h293
                          · rcases p269_3 (m.d 0 2) (by simp) with h294 | h294
                            · rcases p269_3 (m.d 0 3) (by simp) with h295 | h295
                              · linarith only [h295, h4, hlam]
                              · linarith only [h295, h8, hlam]
                            · linarith only [h294, h6, hlam]
                          · linarith only [h293, h3, hlam]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h1, hlam, p269_1]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h4, hlam, p269_1]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h2, h258, h263, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p269_1, u3elo0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h2, h258, h263, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p269_1, u3elo0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h2, hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h5, hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h7, hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h9, hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h3, hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h6, hlam, p269_1]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h8, hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h2, h258, h263, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p269_1, u3elo0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [hlam, p269_0]
                  · linarith only [h264, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h263, h7, hc23, hlam, hphi, u3elo0]
            · linarith only [h260, h8, hc13, hlam, hphi, u3elo0]
          · linarith only [h257, h259, h6, h8, hc23, hlam, hphi, u3elo0]
        · linarith only [h257, h258, h5, h9, hc23, hc45, hlam, hphi, ht34]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h320 | h320
        · rcases m.htr 1 2 5 (by decide) (by decide) with h321 | h321
          · rcases m.htr 1 3 5 (by decide) (by decide) with h322 | h322
            · rcases m.htr 1 4 5 (by decide) (by decide) with h323 | h323
              · linarith only [h257, h320, h323, h4, h9, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h325 | h325
                · rcases m.htr 2 3 5 (by decide) (by decide) with h326 | h326
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h327 | h327
                    · linarith only [h2, h320, h327, h9, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h329 | h329
                      · linarith only [h2, h320, h325, h329, h9, hlam]
                      · rcases h0bigk with h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h0, h321, h327, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p331_1]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h257, h321, h327, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p331_1]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          rcases p331_3 (m.d 0 1) (by simp) with h335 | h335
                          · rcases p331_3 (m.d 0 2) (by simp) with h336 | h336
                            · linarith only [h0, h336, hlam]
                            · linarith only [h336, h5, hlam]
                          · linarith only [h2, h335, hlam]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          rcases p331_3 (m.d 0 1) (by simp) with h340 | h340
                          · rcases p331_3 (m.d 0 2) (by simp) with h341 | h341
                            · linarith only [h0, h341, hlam]
                            · linarith only [h341, h6, hlam]
                          · linarith only [h3, h340, hlam]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h0, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h257, h321, h325, h327, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p331_1]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          rcases p331_3 (m.d 0 1) (by simp) with h348 | h348
                          · rcases p331_3 (m.d 0 2) (by simp) with h349 | h349
                            · rcases p331_3 (m.d 0 3) (by simp) with h350 | h350
                              · linarith only [h350, h4, hlam]
                              · linarith only [h350, h7, hlam]
                            · linarith only [h349, h5, hlam]
                          · linarith only [h2, h348, hlam]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          rcases p331_3 (m.d 0 1) (by simp) with h355 | h355
                          · rcases p331_3 (m.d 0 2) (by simp) with h356 | h356
                            · rcases p331_3 (m.d 0 3) (by simp) with h357 | h357
                              · linarith only [h357, h4, hlam]
                              · linarith only [h357, h8, hlam]
                            · linarith only [h356, h6, hlam]
                          · linarith only [h3, h355, hlam]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h1, hlam, p331_1]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h4, hlam, p331_1]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h2, h320, h325, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p331_1, u3elo0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h3, h320, h323, h325, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p331_1, u3elo0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h2, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h5, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h7, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h9, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h3, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h6, hlam, p331_1]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h8, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h2, h320, h325, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p331_1, u3elo0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [hlam, p331_0]
                  · linarith only [h257, h326, hc12, hlam, hphi, ht23, u3elo4]
                · linarith only [h257, h325, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h257, h320, h322, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h380 | h380
            · rcases m.htr 1 4 5 (by decide) (by decide) with h381 | h381
              · linarith only [h2, h320, h321, h381, h6, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h383 | h383
                · rcases m.htr 2 3 5 (by decide) (by decide) with h384 | h384
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h385 | h385
                    · linarith only [h320, h321, h385, h6, h9, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h387 | h387
                      · linarith only [h320, h321, h383, h387, h6, h9, hlam]
                      · rcases h0bigk with h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [hlam, p389_0]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h0, h320, h383, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p389_1]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h1, h320, h321, h380, h383, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p389_1]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          rcases p389_3 (m.d 0 1) (by simp) with h393 | h393
                          · rcases p389_3 (m.d 0 2) (by simp) with h394 | h394
                            · linarith only [h0, h394, hlam]
                            · linarith only [h394, h5, hlam]
                          · linarith only [h2, h393, hlam]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h320, h321, h383, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p389_1]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h0, hlam, p389_0]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [hlam, p389_0]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h320, h321, h383, h384, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p389_1]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          rcases p389_3 (m.d 0 1) (by simp) with h402 | h402
                          · rcases p389_3 (m.d 0 2) (by simp) with h403 | h403
                            · rcases p389_3 (m.d 0 3) (by simp) with h404 | h404
                              · linarith only [h4, h404, hlam]
                              · linarith only [h404, h7, hlam]
                            · linarith only [h403, h5, hlam]
                          · linarith only [h2, h402, hlam]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h0, h320, h321, h383, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p389_1]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h1, hlam, p389_1]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h4, hlam, p389_1]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [hlam, p389_0]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h2, h320, h383, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p389_1, u3elo0]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h320, h321, h383, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p389_1, u3elo0]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h2, hlam, p389_0]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h5, hlam, p389_0]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h7, hlam, p389_0]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [hlam, p389_0]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h9, hlam, p389_0]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h3, hlam, p389_0]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h6, hlam, p389_1]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h8, hlam, p389_0]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [h2, h320, h383, h9, hc34, hc45, hlam, hphi, p389_1]
                        · have p389_0 := h389c.1
                          have p389_1 := h389c.2.1
                          have p389_2 := h389c.2.2.1
                          have p389_3 := h389c.2.2.2
                          linarith only [hlam, p389_0]
                  · linarith only [h380, h384, hc23, hlam, hphi, u3elo1]
                · linarith only [h257, h383, h7, hc13, hlam, hphi, u3elo0]
            · linarith only [h257, h380, h8, hc12, hlam, hphi, ht23, u3elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h428 | h428
          · rcases m.htr 1 3 5 (by decide) (by decide) with h429 | h429
            · rcases m.htr 1 4 5 (by decide) (by decide) with h430 | h430
              · linarith only [h320, h428, h430, h5, h9, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h320, h428, h430, hlam]
            · linarith only [h257, h428, h429, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h434 | h434
            · rcases m.htr 1 4 5 (by decide) (by decide) with h435 | h435
              · linarith only [h2, h320, h435, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h437 | h437
                · rcases m.htr 2 3 5 (by decide) (by decide) with h438 | h438
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h439 | h439
                    · linarith only [h439, h5, h9, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h441 | h441
                      · linarith only [h320, h441, h5, h9, hc12, hlam, hphi, ht23, u3elo3]
                      · rcases h0bigk with h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [hlam, p443_0]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h320, h4, h438, h439, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p443_1]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h1, h434, h441, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p443_1]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h320, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p443_1]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h320, h439, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p443_1]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h0, hlam, p443_0]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [hlam, p443_0]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h320, h4, h438, h439, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p443_1]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h0, h320, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p443_1]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h0, h320, h439, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p443_1]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h1, hlam, p443_1]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h4, hlam, p443_1]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [hlam, p443_0]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h320, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p443_1]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h320, h439, h6, hc12, hlam, hphi, ht23, p443_1, u3elo0]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h2, hlam, p443_0]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h5, hlam, p443_0]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h7, hlam, p443_0]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [hlam, p443_0]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h9, hlam, p443_0]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h3, hlam, p443_0]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h6, hlam, p443_1]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h8, hlam, p443_0]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [h320, h5, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p443_1]
                        · have p443_0 := h443c.1
                          have p443_1 := h443c.2.1
                          have p443_2 := h443c.2.2.1
                          have p443_3 := h443c.2.2.2
                          linarith only [hlam, p443_0]
                  · linarith only [h434, h438, hc23, hlam, hphi, u3elo1]
                · linarith only [h257, h437, h7, hc13, hlam, hphi, u3elo0]
            · linarith only [h257, h434, h8, hc12, hlam, hphi, ht23, u3elo0]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h472 | h472
    · linarith only [h472, h7, h8, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h474 | h474
      · rcases m.htr 1 2 4 (by decide) (by decide) with h475 | h475
        · rcases m.htr 1 2 5 (by decide) (by decide) with h476 | h476
          · rcases m.htr 1 3 5 (by decide) (by decide) with h477 | h477
            · linarith only [h1, h477, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h479 | h479
              · linarith only [h2, h472, h479, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h481 | h481
                · rcases m.htr 2 3 5 (by decide) (by decide) with h482 | h482
                  · linarith only [h1, h474, h482, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h484 | h484
                    · linarith only [h2, h472, h475, h484, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h486 | h486
                      · linarith only [h1, h472, h474, h481, h486, h8, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · rcases h0bigk with h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h0, h476, h482, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          rcases p488_3 (m.d 0 1) (by simp) with h492 | h492
                          · rcases p488_3 (m.d 0 2) (by simp) with h493 | h493
                            · linarith only [h0, h493, hlam]
                            · linarith only [h493, h5, hlam]
                          · linarith only [h2, h492, hlam]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h1, h474, h481, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h0, hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h1, h474, h481, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          rcases p488_3 (m.d 0 1) (by simp) with h501 | h501
                          · rcases p488_3 (m.d 0 2) (by simp) with h502 | h502
                            · rcases p488_3 (m.d 0 3) (by simp) with h503 | h503
                              · linarith only [h4, h503, hlam]
                              · linarith only [h503, h7, hlam]
                            · linarith only [h5, h502, hlam]
                          · linarith only [h2, h501, hlam]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h0, h1, h474, h481, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h1, hlam, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h4, hlam, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h2, h475, h481, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p488_1, u3elo4]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h8, hlam, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h2, hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h5, hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h7, hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h472, hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h3, hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h6, hlam, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h1, h474, h481, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h2, h475, h481, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p488_1, u3elo4]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [hlam, p488_0]
                · linarith only [h481, h7, hc23, hlam, hphi, u3elo0]
          · linarith only [h474, h476, h6, h8, hc23, hlam, hphi, u3elo4]
        · linarith only [h474, h475, h5, h7, h8, hc23, hlam, hphi, u3elo4]
      · linarith only [h4, h474, h8, hc12, hlam, hphi, ht23, u3elo4]

end R2N4
