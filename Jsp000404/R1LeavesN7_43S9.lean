import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
    · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
          · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
              · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                      · linarith only [h0, h10, h14, h17, hc01, hc45, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h10, h14, h16, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                      · linarith only [h16, h20, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                      · rcases h0bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h15, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h14, h16, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h14, h16, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h0, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h14, h16, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h0, h14, h16, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h0, h14, h16, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h1, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h4, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h14, h16, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p22_1, u3elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p22_1, u3elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h2, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h5, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h7, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h3, h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p22_1, u3elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h3, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h6, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h8, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h9, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                  · linarith only [h14, h15, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                · linarith only [h14, h7, hc23, hlam, hphi, u3elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h50 | h50
                · rcases m.htr 2 3 5 (by decide) (by decide) with h51 | h51
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h52 | h52
                    · linarith only [h0, h10, h13, h50, h52, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                      · linarith only [h12, h13, h54, hlam]
                      · rcases h0bigk with h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [hlam, p56_0]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p56_1]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p56_1]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [h12, h13, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p56_1]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [h12, h13, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p56_1]
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
                          linarith only [h12, h13, h8, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p56_1]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [h0, h12, h13, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p56_1]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [h0, h12, h13, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p56_1]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [h1, hlam, p56_1]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [h4, hlam, p56_1]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [hlam, p56_0]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p56_1, u3elo0]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [h12, h13, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p56_1, u3elo0]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [h2, hlam, p56_0]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [h5, hlam, p56_0]
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
                          linarith only [h12, h13, h9, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p56_1]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [h3, hlam, p56_0]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [h6, hlam, p56_1]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [h8, hlam, p56_0]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [h9, hlam, p56_1]
                        · have p56_0 := h56c.1
                          have p56_1 := h56c.2.1
                          have p56_2 := h56c.2.2.1
                          have p56_3 := h56c.2.2.2
                          linarith only [hlam, p56_0]
                  · linarith only [h50, h51, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                · linarith only [h50, h7, hc23, hlam, hphi, u3elo0]
            · linarith only [h12, h7, hc13, hlam, hphi, u3elo0]
          · linarith only [h10, h11, h6, h7, h9, hc23, hlam, hphi, u3elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h86 | h86
          · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
            · rcases m.htr 1 4 5 (by decide) (by decide) with h88 | h88
              · rcases m.htr 2 3 4 (by decide) (by decide) with h89 | h89
                · rcases m.htr 2 3 5 (by decide) (by decide) with h90 | h90
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h91 | h91
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h92 | h92
                      · rcases h0bigk with h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [hlam, p93_0]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [h0, h86, h90, h92, hc01, hc45, hlam, hphi, ht0b, ht5b, p93_1]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [h10, h4, h86, h90, h92, hc01, hc45, hlam, hphi, ht0b, ht5b, p93_1]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [h5, h89, h92, hc01, hc45, hlam, hphi, ht0b, ht5b, p93_1]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          rcases p93_3 (m.d 0 1) (by simp) with h98 | h98
                          · rcases p93_3 (m.d 0 2) (by simp) with h99 | h99
                            · linarith only [h0, h99, hlam]
                            · linarith only [h6, h99, hlam]
                          · linarith only [h3, h98, hlam]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [h0, hlam, p93_0]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [hlam, p93_0]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [h10, h4, h86, h90, h92, hc02, hc45, hlam, hphi, ht0b, ht5b, p93_1]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [h0, h5, h89, h92, hc01, hc45, hlam, hphi, ht0b, ht5b, p93_1]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          rcases p93_3 (m.d 0 1) (by simp) with h107 | h107
                          · rcases p93_3 (m.d 0 2) (by simp) with h108 | h108
                            · rcases p93_3 (m.d 0 3) (by simp) with h109 | h109
                              · linarith only [h109, h4, hlam]
                              · linarith only [h109, h8, hlam]
                            · linarith only [h108, h6, hlam]
                          · linarith only [h107, h3, hlam]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [h1, hlam, p93_1]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [h4, hlam, p93_1]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [hlam, p93_0]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [h5, h89, h92, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p93_1, u3elo0]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p93_1, u3elo0]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [h2, hlam, p93_0]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [h5, hlam, p93_0]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [h7, hlam, p93_0]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [hlam, p93_0]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [h6, h7, h90, h92, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p93_1, u3elo0]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [h3, hlam, p93_0]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [h6, hlam, p93_1]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [h8, hlam, p93_0]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [h9, hlam, p93_1]
                        · have p93_0 := h93c.1
                          have p93_1 := h93c.2.1
                          have p93_2 := h93c.2.2.1
                          have p93_3 := h93c.2.2.2
                          linarith only [hlam, p93_0]
                      · linarith only [h10, h4, h86, h91, h92, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h130 | h130
                      · linarith only [h130, h89, h91, hlam]
                      · rcases h0bigk with h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h0, h86, hc01, hc25, hlam, hphi, ht0b, ht5b, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h89, h9, h91, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h3, h88, h89, h91, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h0, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h3, h8, h88, h89, h91, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h0, h89, h9, h91, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h0, h3, h88, h89, h91, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h1, hlam, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h4, hlam, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h2, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p132_1, u3elo0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h3, h88, h89, h91, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p132_1, u3elo0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h2, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h5, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h7, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h3, h88, h89, h91, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h3, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h6, hlam, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h8, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h9, hlam, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                  · linarith only [h10, h8, h90, hc13, hlam, hphi, u3elo0]
                · linarith only [h10, h86, h89, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h160 | h160
                · rcases m.htr 2 3 5 (by decide) (by decide) with h161 | h161
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h162 | h162
                    · linarith only [h10, h162, h4, h86, h88, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h164 | h164
                      · linarith only [h164, h87, h88, hlam]
                      · rcases h0bigk with h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h0, h86, hc01, hc25, hlam, hphi, ht0b, ht5b, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h1, h10, h86, hc01, hc25, hlam, hphi, ht0b, ht5b, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h87, h88, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h87, h88, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h0, hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h8, h87, h88, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h0, h87, h88, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h0, h87, h88, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h1, hlam, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h4, hlam, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p166_1, u3elo0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h87, h88, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p166_1, u3elo0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h2, hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h5, hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h7, hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h87, h88, h9, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h3, hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h6, hlam, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h8, hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h9, hlam, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hlam, p166_0]
                  · linarith only [h161, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h10, h160, h86, h87, h88, h9, hc05, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h10, h7, h86, h87, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h195 | h195
            · rcases m.htr 1 4 5 (by decide) (by decide) with h196 | h196
              · rcases m.htr 2 3 4 (by decide) (by decide) with h197 | h197
                · rcases m.htr 2 3 5 (by decide) (by decide) with h198 | h198
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h199 | h199
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h200 | h200
                      · rcases h0bigk with h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h197, h199, h4, h86, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h1, h195, h200, hc01, hc45, hlam, hphi, ht0b, ht5b, p201_1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h199, h5, h86, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h6, h86, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h0, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h1, h195, h200, hc02, hc45, hlam, hphi, ht0b, ht5b, p201_1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h0, h199, h5, h86, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h0, h6, h86, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h1, hlam, p201_1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h4, hlam, p201_1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h199, h5, h86, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h6, h86, hc12, hlam, hphi, ht23, p201_1, u3elo0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h2, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h5, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h7, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h6, h86, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h3, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h6, hlam, p201_1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h8, hlam, p201_0]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [h9, hlam, p201_1]
                        · have p201_0 := h201c.1
                          have p201_1 := h201c.2.1
                          have p201_2 := h201c.2.2.1
                          have p201_3 := h201c.2.2.2
                          linarith only [hlam, p201_0]
                      · rcases h0bigk with h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h10, h195, h196, h200, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h10, h195, h196, h200, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h196, h2, h200, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h10, h195, h196, h200, h4, h6, h86, hc01, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p227_1, u3elo0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h0, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h10, h195, h196, h200, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h0, h196, h2, h200, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h0, h10, h195, h196, h200, h4, h6, h86, hc01, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p227_1, u3elo0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h1, hlam, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h4, hlam, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h196, h2, h200, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p227_1, u3elo0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h6, h86, hc12, hlam, hphi, ht23, p227_1, u3elo0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h2, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h5, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h7, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h6, h86, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h3, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h6, hlam, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h8, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h9, hlam, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [hlam, p227_0]
                    · linarith only [h10, h195, h196, h199, h4, h86, hc12, hlam, hphi, ht23, u3elo0]
                  · linarith only [h10, h198, h8, hc13, hlam, hphi, u3elo0]
                · linarith only [h10, h197, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h256 | h256
                · rcases m.htr 2 3 5 (by decide) (by decide) with h257 | h257
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h258 | h258
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h259 | h259
                      · linarith only [h195, h196, h259, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · rcases h0bigk with h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [hlam, p261_0]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h10, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p261_1]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p261_1]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h195, h196, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p261_1]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h6, h86, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p261_1]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h0, hlam, p261_0]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [hlam, p261_0]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h6, h8, h86, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p261_1]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h0, h195, h196, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p261_1]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h0, h6, h86, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p261_1]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h1, hlam, p261_1]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h4, hlam, p261_1]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [hlam, p261_0]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p261_1, u3elo0]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h6, h86, hc12, hlam, hphi, ht23, p261_1, u3elo0]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h2, hlam, p261_0]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h5, hlam, p261_0]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h7, hlam, p261_0]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [hlam, p261_0]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h6, h86, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p261_1]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h3, hlam, p261_0]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h6, hlam, p261_1]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h8, hlam, p261_0]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [h9, hlam, p261_1]
                        · have p261_0 := h261c.1
                          have p261_1 := h261c.2.1
                          have p261_2 := h261c.2.2.1
                          have p261_3 := h261c.2.2.2
                          linarith only [hlam, p261_0]
                    · linarith only [h258, h7, h86, h9, hc12, hlam, hphi, ht23, u3elo0]
                  · linarith only [h257, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h10, h195, h196, h256, h7, h9, hc12, hlam, hphi, ht23, u3elo0]
            · linarith only [h195, h7, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h291 | h291
        · rcases m.htr 1 2 5 (by decide) (by decide) with h292 | h292
          · rcases m.htr 1 3 4 (by decide) (by decide) with h293 | h293
            · rcases m.htr 1 4 5 (by decide) (by decide) with h294 | h294
              · linarith only [h2, h294, h9, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h296 | h296
                · rcases m.htr 2 3 5 (by decide) (by decide) with h297 | h297
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h298 | h298
                    · linarith only [h298, h5, h9, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h300 | h300
                      · linarith only [h291, h296, h300, h9, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h0bigk with h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h0, h291, h297, h300, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p302_1]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h1, h291, h297, h300, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p302_1]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          rcases p302_3 (m.d 0 1) (by simp) with h306 | h306
                          · rcases p302_3 (m.d 0 2) (by simp) with h307 | h307
                            · linarith only [h0, h307, hlam]
                            · linarith only [h307, h5, hlam]
                          · linarith only [h2, h306, hlam]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          rcases p302_3 (m.d 0 1) (by simp) with h311 | h311
                          · rcases p302_3 (m.d 0 2) (by simp) with h312 | h312
                            · linarith only [h0, h312, hlam]
                            · linarith only [h312, h6, hlam]
                          · linarith only [h3, h311, hlam]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h0, hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h1, h291, h297, h300, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p302_1]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          rcases p302_3 (m.d 0 1) (by simp) with h319 | h319
                          · rcases p302_3 (m.d 0 2) (by simp) with h320 | h320
                            · rcases p302_3 (m.d 0 3) (by simp) with h321 | h321
                              · linarith only [h321, h4, hlam]
                              · linarith only [h321, h7, hlam]
                            · linarith only [h320, h5, hlam]
                          · linarith only [h2, h319, hlam]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          rcases p302_3 (m.d 0 1) (by simp) with h326 | h326
                          · rcases p302_3 (m.d 0 2) (by simp) with h327 | h327
                            · rcases p302_3 (m.d 0 3) (by simp) with h328 | h328
                              · linarith only [h328, h4, hlam]
                              · linarith only [h328, h8, hlam]
                            · linarith only [h327, h6, hlam]
                          · linarith only [h3, h326, hlam]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h1, hlam, p302_1]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h4, hlam, p302_1]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h2, h293, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p302_1, u3elo0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p302_1, u3elo0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h2, hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h5, hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h7, hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h9, hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h3, hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h6, hlam, p302_1]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h8, hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h2, h293, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p302_1, u3elo0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [hlam, p302_0]
                  · linarith only [h297, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h293, h296, hc23, hlam, hphi, u3elo1]
            · linarith only [h293, h7, hc13, hlam, hphi, u3elo0]
          · linarith only [h291, h292, h6, h8, hc23, hlam, hphi, u3elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h352 | h352
          · rcases m.htr 1 3 4 (by decide) (by decide) with h353 | h353
            · rcases m.htr 1 4 5 (by decide) (by decide) with h354 | h354
              · linarith only [h2, h354, h9, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h356 | h356
                · rcases m.htr 2 3 5 (by decide) (by decide) with h357 | h357
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h358 | h358
                    · linarith only [h358, h5, h9, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h360 | h360
                      · linarith only [h2, h353, h360, h9, hlam]
                      · rcases h0bigk with h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h0, h352, h356, h358, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h291, h352, h356, h358, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          rcases p362_3 (m.d 0 1) (by simp) with h366 | h366
                          · rcases p362_3 (m.d 0 2) (by simp) with h367 | h367
                            · linarith only [h0, h367, hlam]
                            · linarith only [h367, h5, hlam]
                          · linarith only [h2, h366, hlam]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          rcases p362_3 (m.d 0 1) (by simp) with h371 | h371
                          · rcases p362_3 (m.d 0 2) (by simp) with h372 | h372
                            · linarith only [h0, h372, hlam]
                            · linarith only [h372, h6, hlam]
                          · linarith only [h3, h371, hlam]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h0, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h291, h352, h356, h358, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          rcases p362_3 (m.d 0 1) (by simp) with h379 | h379
                          · rcases p362_3 (m.d 0 2) (by simp) with h380 | h380
                            · rcases p362_3 (m.d 0 3) (by simp) with h381 | h381
                              · linarith only [h381, h4, hlam]
                              · linarith only [h381, h7, hlam]
                            · linarith only [h380, h5, hlam]
                          · linarith only [h2, h379, hlam]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          rcases p362_3 (m.d 0 1) (by simp) with h386 | h386
                          · rcases p362_3 (m.d 0 2) (by simp) with h387 | h387
                            · rcases p362_3 (m.d 0 3) (by simp) with h388 | h388
                              · linarith only [h388, h4, hlam]
                              · linarith only [h388, h8, hlam]
                            · linarith only [h387, h6, hlam]
                          · linarith only [h3, h386, hlam]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h1, hlam, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h4, hlam, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h2, h353, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p362_1, u3elo0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h3, h352, h356, h358, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p362_1, u3elo0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h2, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h5, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h7, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h9, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h3, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h6, hlam, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h8, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h2, h353, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p362_1, u3elo0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hlam, p362_0]
                  · linarith only [h291, h357, hc12, hlam, hphi, ht23, u3elo4]
                · linarith only [h291, h352, h356, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
            · linarith only [h353, h7, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h411 | h411
            · rcases m.htr 1 4 5 (by decide) (by decide) with h412 | h412
              · linarith only [h2, h412, h9, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h414 | h414
                · rcases m.htr 2 3 5 (by decide) (by decide) with h415 | h415
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h416 | h416
                    · linarith only [h416, h5, h9, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h418 | h418
                      · linarith only [h352, h418, h6, h9, hc12, hlam, hphi, ht23, u3elo3]
                      · rcases h0bigk with h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [hlam, p420_0]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [h291, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p420_1]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [h4, h415, hc01, hc35, hlam, hphi, ht0b, ht5b, p420_1]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          rcases p420_3 (m.d 0 1) (by simp) with h424 | h424
                          · rcases p420_3 (m.d 0 2) (by simp) with h425 | h425
                            · linarith only [h0, h425, hlam]
                            · linarith only [h425, h5, hlam]
                          · linarith only [h2, h424, hlam]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [h352, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p420_1]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [h0, hlam, p420_0]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [hlam, p420_0]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [h291, h4, h411, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p420_1]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          rcases p420_3 (m.d 0 1) (by simp) with h433 | h433
                          · rcases p420_3 (m.d 0 2) (by simp) with h434 | h434
                            · rcases p420_3 (m.d 0 3) (by simp) with h435 | h435
                              · linarith only [h4, h435, hlam]
                              · linarith only [h435, h7, hlam]
                            · linarith only [h434, h5, hlam]
                          · linarith only [h2, h433, hlam]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [h0, h352, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p420_1]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [h1, hlam, p420_1]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [h4, hlam, p420_1]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [hlam, p420_0]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p420_1, u3elo0]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [h352, h6, hc12, hlam, hphi, ht23, p420_1, u3elo0]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [h2, hlam, p420_0]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [h5, hlam, p420_0]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [h7, hlam, p420_0]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [hlam, p420_0]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [h9, hlam, p420_0]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [h3, hlam, p420_0]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [h6, hlam, p420_1]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [h8, hlam, p420_0]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [h2, h9, hc14, hc45, hlam, hphi, p420_1]
                        · have p420_0 := h420c.1
                          have p420_1 := h420c.2.1
                          have p420_2 := h420c.2.2.1
                          have p420_3 := h420c.2.2.2
                          linarith only [hlam, p420_0]
                  · linarith only [h415, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h291, h414, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h411, h7, hc13, hlam, hphi, u3elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h459 | h459
      · linarith only [h459, h7, h8, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h461 | h461
        · rcases m.htr 1 2 5 (by decide) (by decide) with h462 | h462
          · rcases m.htr 1 3 4 (by decide) (by decide) with h463 | h463
            · rcases m.htr 1 4 5 (by decide) (by decide) with h464 | h464
              · linarith only [h2, h459, h464, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h466 | h466
                · rcases m.htr 2 3 5 (by decide) (by decide) with h467 | h467
                  · linarith only [h1, h461, h467, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h469 | h469
                    · linarith only [h1, h459, h461, h466, h469, h8, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h471 | h471
                      · linarith only [h459, h471, h7, h8, hlam]
                      · rcases h0bigk with h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [hlam, p473_0]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h4, h466, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p473_1]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h1, h461, h466, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p473_1]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          rcases p473_3 (m.d 0 1) (by simp) with h477 | h477
                          · rcases p473_3 (m.d 0 2) (by simp) with h478 | h478
                            · linarith only [h0, h478, hlam]
                            · linarith only [h478, h5, hlam]
                          · linarith only [h2, h477, hlam]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h1, h461, h466, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p473_1]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h0, hlam, p473_0]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [hlam, p473_0]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h1, h461, h466, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p473_1]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          rcases p473_3 (m.d 0 1) (by simp) with h486 | h486
                          · rcases p473_3 (m.d 0 2) (by simp) with h487 | h487
                            · rcases p473_3 (m.d 0 3) (by simp) with h488 | h488
                              · linarith only [h4, h488, hlam]
                              · linarith only [h488, h7, hlam]
                            · linarith only [h487, h5, hlam]
                          · linarith only [h2, h486, hlam]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h0, h1, h461, h466, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p473_1]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h1, hlam, p473_1]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h4, hlam, p473_1]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [hlam, p473_0]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h2, h463, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p473_1, u3elo4]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h8, hlam, p473_1]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h2, hlam, p473_0]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h5, hlam, p473_0]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h7, hlam, p473_0]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [hlam, p473_0]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h459, hlam, p473_0]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h3, hlam, p473_0]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h6, hlam, p473_1]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h0, h6, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p473_1]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [h2, h463, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p473_1, u3elo4]
                        · have p473_0 := h473c.1
                          have p473_1 := h473c.2.1
                          have p473_2 := h473c.2.2.1
                          have p473_3 := h473c.2.2.2
                          linarith only [hlam, p473_0]
                · linarith only [h1, h463, h466, hc23, hlam, hphi, u3elo0]
            · linarith only [h463, h7, h8, hc13, hlam, hphi, u3elo4]
          · linarith only [h461, h462, h6, h8, hc23, hlam, hphi, u3elo4]
        · linarith only [h4, h461, h8, hc12, hlam, hphi, ht23, u3elo4]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h513 | h513
    · rcases m.htr 0 4 5 (by decide) (by decide) with h514 | h514
      · rcases m.htr 1 2 3 (by decide) (by decide) with h515 | h515
        · rcases m.htr 1 2 5 (by decide) (by decide) with h516 | h516
          · rcases m.htr 1 3 4 (by decide) (by decide) with h517 | h517
            · linarith only [h513, h517, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h519 | h519
              · rcases m.htr 2 3 4 (by decide) (by decide) with h520 | h520
                · linarith only [h1, h515, h520, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h522 | h522
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h523 | h523
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h524 | h524
                      · rcases h0bigk with h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h4, h522, h524, hc01, hc45, hlam, hphi, ht0b, ht5b, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h1, h515, h522, h524, hc01, hc45, hlam, hphi, ht0b, ht5b, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h1, h515, h522, h524, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          rcases p525_3 (m.d 0 1) (by simp) with h530 | h530
                          · rcases p525_3 (m.d 0 2) (by simp) with h531 | h531
                            · linarith only [h0, h531, hlam]
                            · linarith only [h531, h6, hlam]
                          · linarith only [h3, h530, hlam]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h0, hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h1, h515, h522, h524, hc02, hc45, hlam, hphi, ht0b, ht5b, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h0, h1, h515, h522, h524, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          rcases p525_3 (m.d 0 1) (by simp) with h539 | h539
                          · rcases p525_3 (m.d 0 2) (by simp) with h540 | h540
                            · rcases p525_3 (m.d 0 3) (by simp) with h541 | h541
                              · linarith only [h4, h541, hlam]
                              · linarith only [h513, h541, hlam]
                            · linarith only [h540, h6, hlam]
                          · linarith only [h3, h539, hlam]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h1, hlam, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h4, hlam, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h7, hlam, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h7, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p525_1, u3elo3]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h2, hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h5, hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h1, h515, h522, h524, hc04, hc45, hlam, hphi, ht0b, ht5b, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h3, h516, h522, h524, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p525_1, u3elo3]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h3, hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h6, hlam, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h513, hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h514, hlam, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [hlam, p525_0]
                      · linarith only [h1, h514, h515, h522, h524, h7, hc04, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h2, h519, h520, h522, h523, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h513, h522, h7, hc23, hlam, hphi, u3elo3]
              · linarith only [h513, h514, h515, h517, h519, h7, hc23, hlam, hphi, u3elo3]
          · linarith only [h513, h515, h516, h6, h7, hc23, hlam, hphi, u3elo3]
        · linarith only [h4, h515, h7, hc12, hlam, hphi, ht23, u3elo3]
      · linarith only [h513, h514, h7, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h568 | h568
      · rcases m.htr 1 2 3 (by decide) (by decide) with h569 | h569
        · rcases m.htr 1 2 5 (by decide) (by decide) with h570 | h570
          · rcases m.htr 1 3 4 (by decide) (by decide) with h571 | h571
            · linarith only [h1, h571, h7, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h573 | h573
              · rcases m.htr 2 3 4 (by decide) (by decide) with h574 | h574
                · linarith only [h1, h569, h574, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h576 | h576
                  · linarith only [h1, h513, h569, h576, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h578 | h578
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h579 | h579
                      · rcases h0bigk with h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [hlam, p580_0]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [h0, h570, h576, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p580_1]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          rcases p580_3 (m.d 0 1) (by simp) with h583 | h583
                          · rcases p580_3 (m.d 0 2) (by simp) with h584 | h584
                            · linarith only [h0, h584, hlam]
                            · linarith only [h4, h584, hlam]
                          · linarith only [h1, h583, hlam]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [h5, h578, hc01, hc45, hlam, hphi, ht0b, ht5b, p580_1]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          rcases p580_3 (m.d 0 1) (by simp) with h589 | h589
                          · rcases p580_3 (m.d 0 2) (by simp) with h590 | h590
                            · linarith only [h0, h590, hlam]
                            · linarith only [h590, h6, hlam]
                          · linarith only [h3, h589, hlam]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [h0, hlam, p580_0]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [hlam, p580_0]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          rcases p580_3 (m.d 0 1) (by simp) with h596 | h596
                          · rcases p580_3 (m.d 0 2) (by simp) with h597 | h597
                            · rcases p580_3 (m.d 0 3) (by simp) with h598 | h598
                              · linarith only [h4, h598, hlam]
                              · rcases p580_3 (m.d 0 4) (by simp) with h600 | h600
                                · linarith only [h5, h600, hlam]
                                · linarith only [h600, h7, hlam]
                            · linarith only [h4, h597, hlam]
                          · linarith only [h1, h596, hlam]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [h5, h578, hc02, hc45, hlam, hphi, ht0b, ht5b, p580_1]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          rcases p580_3 (m.d 0 1) (by simp) with h606 | h606
                          · rcases p580_3 (m.d 0 2) (by simp) with h607 | h607
                            · rcases p580_3 (m.d 0 3) (by simp) with h608 | h608
                              · linarith only [h4, h608, hlam]
                              · rcases p580_3 (m.d 0 4) (by simp) with h610 | h610
                                · linarith only [h5, h610, hlam]
                                · linarith only [h568, h610, hlam]
                            · linarith only [h6, h607, hlam]
                          · linarith only [h3, h606, hlam]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [h1, hlam, p580_1]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [h4, hlam, p580_1]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [hlam, p580_0]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [h7, hlam, p580_1]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [h513, hlam, p580_1]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [h2, hlam, p580_0]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [h5, hlam, p580_0]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [h1, h569, h7, hc23, hlam, hphi, p580_1, u3elo3]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [hlam, p580_0]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [h1, h513, h569, h7, hc23, hlam, hphi, p580_1, u3elo3]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [h3, hlam, p580_0]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [h6, hlam, p580_1]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [h1, h513, h569, hc23, hlam, hphi, p580_1, u3elo4]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [h568, hlam, p580_1]
                        · have p580_0 := h580c.1
                          have p580_1 := h580c.2.1
                          have p580_2 := h580c.2.2.1
                          have p580_3 := h580c.2.2.2
                          linarith only [hlam, p580_0]
                      · linarith only [h5, h578, h579, h7, hlam]
                    · linarith only [h2, h573, h574, h578, h7, hc23, hlam, hphi, u3elo3]
              · linarith only [h568, h569, h571, h573, h7, hc23, hlam, hphi, u3elo3]
          · linarith only [h568, h569, h570, h6, h7, hc23, hlam, hphi, u3elo3]
        · linarith only [h4, h569, h7, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h635 | h635
        · rcases m.htr 1 2 5 (by decide) (by decide) with h636 | h636
          · rcases m.htr 1 3 4 (by decide) (by decide) with h637 | h637
            · linarith only [h1, h637, h7, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h639 | h639
              · linarith only [h2, h568, h639, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h641 | h641
                · linarith only [h1, h635, h641, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h643 | h643
                  · linarith only [h1, h513, h635, h643, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h645 | h645
                    · linarith only [h5, h568, h645, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h647 | h647
                      · linarith only [h2, h568, h635, h637, h647, hc23, hlam, hphi, u3elo3]
                      · rcases h0bigk with h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [hlam, p649_0]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [h0, h636, h641, h645, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p649_1]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          rcases p649_3 (m.d 0 1) (by simp) with h652 | h652
                          · rcases p649_3 (m.d 0 2) (by simp) with h653 | h653
                            · linarith only [h0, h653, hlam]
                            · linarith only [h4, h653, hlam]
                          · linarith only [h1, h652, hlam]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          rcases p649_3 (m.d 0 1) (by simp) with h657 | h657
                          · rcases p649_3 (m.d 0 2) (by simp) with h658 | h658
                            · linarith only [h0, h658, hlam]
                            · linarith only [h5, h658, hlam]
                          · linarith only [h2, h657, hlam]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          rcases p649_3 (m.d 0 1) (by simp) with h662 | h662
                          · rcases p649_3 (m.d 0 2) (by simp) with h663 | h663
                            · linarith only [h0, h663, hlam]
                            · linarith only [h6, h663, hlam]
                          · linarith only [h3, h662, hlam]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [h0, hlam, p649_0]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [hlam, p649_0]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          rcases p649_3 (m.d 0 1) (by simp) with h669 | h669
                          · rcases p649_3 (m.d 0 2) (by simp) with h670 | h670
                            · rcases p649_3 (m.d 0 3) (by simp) with h671 | h671
                              · linarith only [h4, h671, hlam]
                              · rcases p649_3 (m.d 0 4) (by simp) with h673 | h673
                                · linarith only [h5, h673, hlam]
                                · linarith only [h673, h7, hlam]
                            · linarith only [h4, h670, hlam]
                          · linarith only [h1, h669, hlam]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          rcases p649_3 (m.d 0 1) (by simp) with h678 | h678
                          · rcases p649_3 (m.d 0 2) (by simp) with h679 | h679
                            · rcases p649_3 (m.d 0 3) (by simp) with h680 | h680
                              · linarith only [h4, h680, hlam]
                              · rcases p649_3 (m.d 0 4) (by simp) with h682 | h682
                                · linarith only [h5, h682, hlam]
                                · rcases p649_3 (m.d 0 5) (by simp) with h684 | h684
                                  · linarith only [h6, h684, hlam]
                                  · linarith only [h568, h684, hlam]
                            · linarith only [h5, h679, hlam]
                          · linarith only [h2, h678, hlam]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          rcases p649_3 (m.d 0 1) (by simp) with h689 | h689
                          · rcases p649_3 (m.d 0 2) (by simp) with h690 | h690
                            · rcases p649_3 (m.d 0 3) (by simp) with h691 | h691
                              · linarith only [h4, h691, hlam]
                              · rcases p649_3 (m.d 0 4) (by simp) with h693 | h693
                                · linarith only [h5, h693, hlam]
                                · rcases p649_3 (m.d 0 5) (by simp) with h695 | h695
                                  · linarith only [h6, h695, hlam]
                                  · rcases h4bigk with h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [hlam, p697_0]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [h568, h635, h637, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p649_1, p697_1]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [h0, h568, h641, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p649_1, p697_1]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [h7, hlam, p697_0]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [h568, hlam, p697_0]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [h2, hlam, p697_1]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [hlam, p697_0]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [h0, h2, h568, h641, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p649_1, p697_1]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [h637, hlam, p697_1]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [h639, hlam, p697_0]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [h5, hlam, p697_1]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [h0, h636, h645, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p697_1]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [hlam, p697_0]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [h641, hlam, p697_1]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [h645, hlam, p697_0]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [h647, hc04, hc45, hlam, hphi, p697_1]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [h647, hc14, hc45, hlam, hphi, p697_1]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [h647, hc24, hc45, hlam, hphi, p697_1]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [hlam, p697_0]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [h647, hlam, p697_0]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      rcases p697_3 (m.d 0 4) (by simp) with h718 | h718
                                      · linarith only [h718, hlam, p697_0]
                                      · rcases p697_3 (m.d 1 4) (by simp) with h720 | h720
                                        · linarith only [h639, h720, hlam]
                                        · rcases p697_3 (m.d 2 4) (by simp) with h722 | h722
                                          · linarith only [h645, h722, hlam]
                                          · rcases p697_3 (m.d 3 4) (by simp) with h724 | h724
                                            · linarith only [h647, h724, hlam]
                                            · linarith only [h7, h724, hlam]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      rcases p697_3 (m.d 0 4) (by simp) with h727 | h727
                                      · linarith only [h568, h727, hlam]
                                      · linarith only [h2, h727, hlam]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      rcases p697_3 (m.d 0 4) (by simp) with h730 | h730
                                      · linarith only [h568, h730, hlam]
                                      · linarith only [h5, h730, hlam]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [h1, h635, h7, hc23, hc45, hlam, hphi, ht34, p697_1]
                                    · have p697_0 := h697c.1
                                      have p697_1 := h697c.2.1
                                      have p697_2 := h697c.2.2.1
                                      have p697_3 := h697c.2.2.2
                                      linarith only [hlam, p697_0]
                            · linarith only [h6, h690, hlam]
                          · linarith only [h3, h689, hlam]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [h1, hlam, p649_1]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [h4, hlam, p649_1]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [hlam, p649_0]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [h7, hlam, p649_1]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [h513, hlam, p649_1]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [h2, hlam, p649_0]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [h5, hlam, p649_0]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [h1, h635, h7, hc23, hlam, hphi, p649_1, u3elo3]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [hlam, p649_0]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [h568, hlam, p649_0]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [h3, hlam, p649_0]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [h6, hlam, p649_1]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [h1, h513, h635, hc23, hlam, hphi, p649_1, u3elo4]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [h513, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p649_1, u3elo4]
                        · have p649_0 := h649c.1
                          have p649_1 := h649c.2.1
                          have p649_2 := h649c.2.2.1
                          have p649_3 := h649c.2.2.2
                          linarith only [hlam, p649_0]
          · linarith only [h513, h6, h635, h636, hc23, hlam, hphi, u3elo4]
        · linarith only [h4, h635, h7, hc12, hlam, hphi, ht23, u3elo3]

end R2N4
