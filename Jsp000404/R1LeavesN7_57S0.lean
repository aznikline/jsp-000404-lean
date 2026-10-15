import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3886000 in
theorem r1l7_10_12_23_L_I_L_0_M_LI_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
      · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
        · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
          · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                      · linarith only [h0, h12, h14, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                      · rcases h0bigk with h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [hlam, p16_0]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h0, h13, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p16_1]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h14, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p16_1]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h14, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p16_1]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          rcases p16_3 (m.d 0 1) (by simp) with h21 | h21
                          · rcases p16_3 (m.d 0 2) (by simp) with h22 | h22
                            · linarith only [h0, h22, hlam]
                            · linarith only [h22, h5, hlam]
                          · linarith only [h21, hlam, p16_0]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h0, hlam, p16_0]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [hlam, p16_0]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h14, h6, h8, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p16_1]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h14, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p16_1, u2elo0]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h14, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p16_1, u2elo0]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h1, hlam, p16_1]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h3, hlam, p16_1]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [hlam, p16_0]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h14, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p16_1, u3elo0]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h14, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p16_1, u3elo0]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h2, hlam, p16_0]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h4, hlam, p16_0]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h6, hlam, p16_0]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [hlam, p16_0]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h14, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p16_1, u2elo0]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h0, h13, h14, h3, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p16_1]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h5, hlam, p16_1]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h7, hlam, p16_0]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [h8, hlam, p16_1]
                        · have p16_0 := h16c.1
                          have p16_1 := h16c.2.1
                          have p16_2 := h16c.2.2.1
                          have p16_3 := h16c.2.2.2
                          linarith only [hlam, p16_0]
                    · linarith only [h0, h11, h12, h13, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h12, h6, hc23, hlam, hphi, u3elo0]
                · linarith only [h10, h11, h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
              · linarith only [h10, h6, h9, hc23, hlam, hphi, u3elo0]
            · linarith only [h3, h9, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h51 | h51
            · rcases m.htr 1 3 4 (by decide) (by decide) with h52 | h52
              · rcases m.htr 1 3 5 (by decide) (by decide) with h53 | h53
                · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h56 | h56
                      · linarith only [h51, h54, h56, h8, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h0bigk with h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          linarith only [hlam, p58_0]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          linarith only [h0, h51, h54, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p58_1]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          rcases p58_3 (m.d 0 1) (by simp) with h61 | h61
                          · rcases p58_3 (m.d 0 2) (by simp) with h62 | h62
                            · linarith only [h0, h62, hlam]
                            · linarith only [h3, h62, hlam]
                          · linarith only [h1, h61, hlam]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          rcases p58_3 (m.d 0 1) (by simp) with h66 | h66
                          · rcases p58_3 (m.d 0 2) (by simp) with h67 | h67
                            · linarith only [h0, h67, hlam]
                            · linarith only [h4, h67, hlam]
                          · linarith only [h2, h66, hlam]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          rcases p58_3 (m.d 0 1) (by simp) with h71 | h71
                          · rcases p58_3 (m.d 0 2) (by simp) with h72 | h72
                            · linarith only [h0, h72, hlam]
                            · linarith only [h5, h72, hlam]
                          · linarith only [h71, hlam, p58_0]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          linarith only [h0, hlam, p58_0]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          linarith only [hlam, p58_0]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          linarith only [h1, h51, h55, h56, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p58_1, u2elo0]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          rcases p58_3 (m.d 0 1) (by simp) with h79 | h79
                          · rcases p58_3 (m.d 0 2) (by simp) with h80 | h80
                            · rcases p58_3 (m.d 0 3) (by simp) with h81 | h81
                              · linarith only [h3, h81, hlam]
                              · linarith only [h6, h81, hlam]
                            · linarith only [h4, h80, hlam]
                          · linarith only [h2, h79, hlam]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          rcases p58_3 (m.d 0 1) (by simp) with h86 | h86
                          · rcases p58_3 (m.d 0 2) (by simp) with h87 | h87
                            · rcases p58_3 (m.d 0 3) (by simp) with h88 | h88
                              · linarith only [h3, h88, hlam]
                              · linarith only [h7, h88, hlam]
                            · linarith only [h5, h87, hlam]
                          · linarith only [h86, hc01, hlam, hphi, ht12, p58_1, u2elo0]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          linarith only [h1, hlam, p58_1]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          linarith only [h3, hlam, p58_1]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          linarith only [hlam, p58_0]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          rcases p58_3 (m.d 0 1) (by simp) with h96 | h96
                          · rcases p58_3 (m.d 0 2) (by simp) with h97 | h97
                            · rcases p58_3 (m.d 0 3) (by simp) with h98 | h98
                              · rcases p58_3 (m.d 0 4) (by simp) with h99 | h99
                                · linarith only [h6, h99, hlam]
                                · rcases p58_3 (m.d 0 5) (by simp) with h101 | h101
                                  · linarith only [h101, h7, hlam]
                                  · linarith only [h101, h8, hlam]
                              · linarith only [h6, h98, hlam]
                            · linarith only [h4, h97, hlam]
                          · linarith only [h2, h96, hlam]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          rcases p58_3 (m.d 0 1) (by simp) with h107 | h107
                          · rcases p58_3 (m.d 0 2) (by simp) with h108 | h108
                            · rcases p58_3 (m.d 0 3) (by simp) with h109 | h109
                              · rcases p58_3 (m.d 0 4) (by simp) with h110 | h110
                                · linarith only [h110, h6, hlam]
                                · rcases p58_3 (m.d 0 5) (by simp) with h112 | h112
                                  · linarith only [h112, h7, hlam]
                                  · rcases h0emin with h114 | h114 | h114 | h114 | h114
                                    · rcases h3bigk with h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [hlam, p115_0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [h51, h55, h56, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p115_1, u3elo0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [h55, h56, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p115_1, u3elo0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        rcases p115_3 (m.d 0 3) (by simp) with h119 | h119
                                        · rcases p115_3 (m.d 1 3) (by simp) with h120 | h120
                                          · linarith only [h1, h120, hlam]
                                          · linarith only [h120, h52, hlam]
                                        · linarith only [h119, hlam, p115_0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        rcases p115_3 (m.d 0 3) (by simp) with h124 | h124
                                        · rcases p115_3 (m.d 1 3) (by simp) with h125 | h125
                                          · linarith only [h1, h125, hlam]
                                          · linarith only [h125, h53, hlam]
                                        · linarith only [h124, hlam, p115_0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [h1, hlam, p115_0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [hlam, p115_0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [h55, h56, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p115_1, u3elo1]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        rcases p115_3 (m.d 0 3) (by simp) with h132 | h132
                                        · rcases p115_3 (m.d 1 3) (by simp) with h133 | h133
                                          · rcases p115_3 (m.d 2 3) (by simp) with h134 | h134
                                            · linarith only [h134, h51, hlam]
                                            · linarith only [h134, h54, hlam]
                                          · linarith only [h133, hlam, p115_0]
                                        · linarith only [h132, h6, hlam]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        rcases p115_3 (m.d 0 3) (by simp) with h139 | h139
                                        · rcases p115_3 (m.d 1 3) (by simp) with h140 | h140
                                          · rcases p115_3 (m.d 2 3) (by simp) with h141 | h141
                                            · linarith only [h141, h51, hlam]
                                            · linarith only [h141, h55, hlam]
                                          · linarith only [h140, hlam, p115_0]
                                        · linarith only [h139, h7, hlam]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [h3, hlam, p115_0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [h51, hlam, p115_0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [hlam, p115_0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p115_1, u2elo0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [h0, h51, h56, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p115_1]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [h6, hlam, p115_0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [h52, hlam, p115_0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [h54, hlam, p115_0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [hlam, p115_0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [h56, hlam, p115_1]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [h7, hlam, p115_0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [h53, hlam, p115_0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [h55, hlam, p115_0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p115_1, u3elo0]
                                      · have p115_0 := h115c.1
                                        have p115_1 := h115c.2.1
                                        have p115_2 := h115c.2.2.1
                                        have p115_3 := h115c.2.2.2
                                        linarith only [hlam, p115_0]
                                    · linarith only [h114, hlam, ht01, ht12, u2elo0]
                                    · linarith only [h114, hlam, ht01, ht12, ht23, u3elo0]
                                    · linarith only [h114, h8, hc45, hlam, ht01, ht12, ht23, ht34]
                                    · linarith only [h114, h5, hlam, ht01, ht12, u2elo0]
                              · linarith only [h109, h7, hlam]
                            · linarith only [h108, h5, hlam]
                          · linarith only [h107, hc01, hlam, hphi, ht12, ht23, p58_1, u3elo0]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          linarith only [h2, hlam, p58_0]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          linarith only [h4, hlam, p58_0]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          linarith only [h6, hlam, p58_0]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          linarith only [hlam, p58_0]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          linarith only [h8, hlam, p58_0]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          linarith only [h0, h51, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p58_1]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          linarith only [h5, hlam, p58_1]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          linarith only [h7, hlam, p58_0]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          rcases p58_3 (m.d 0 1) (by simp) with h176 | h176
                          · rcases p58_3 (m.d 0 2) (by simp) with h177 | h177
                            · rcases p58_3 (m.d 0 3) (by simp) with h178 | h178
                              · rcases p58_3 (m.d 0 4) (by simp) with h179 | h179
                                · linarith only [h179, h8, hlam]
                                · rcases p58_3 (m.d 0 5) (by simp) with h181 | h181
                                  · rcases h0emin with h182 | h182 | h182 | h182 | h182
                                    · rcases h3bigk with h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [hc13, hlam, hphi, p183_1, u3elo0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h55, h56, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p183_1, u3elo0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        rcases p183_3 (m.d 0 3) (by simp) with h187 | h187
                                        · rcases p183_3 (m.d 1 3) (by simp) with h188 | h188
                                          · linarith only [h1, h188, hlam]
                                          · linarith only [h188, h52, hlam]
                                        · linarith only [h187, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        rcases p183_3 (m.d 0 3) (by simp) with h192 | h192
                                        · rcases p183_3 (m.d 1 3) (by simp) with h193 | h193
                                          · linarith only [h1, h193, hlam]
                                          · linarith only [h193, h53, hlam]
                                        · linarith only [h192, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h1, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h55, h56, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p183_1, u3elo1]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        rcases p183_3 (m.d 0 3) (by simp) with h200 | h200
                                        · rcases p183_3 (m.d 1 3) (by simp) with h201 | h201
                                          · rcases p183_3 (m.d 2 3) (by simp) with h202 | h202
                                            · linarith only [h202, h51, hlam]
                                            · linarith only [h202, h54, hlam]
                                          · linarith only [h201, hlam, p183_0]
                                        · linarith only [h200, h6, hlam]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        rcases p183_3 (m.d 0 3) (by simp) with h207 | h207
                                        · rcases p183_3 (m.d 1 3) (by simp) with h208 | h208
                                          · rcases p183_3 (m.d 2 3) (by simp) with h209 | h209
                                            · linarith only [h209, h51, hlam]
                                            · linarith only [h209, h55, hlam]
                                          · linarith only [h208, hlam, p183_0]
                                        · linarith only [h207, h7, hlam]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h3, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h51, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p183_1, u2elo0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h0, h51, h56, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p183_1, u2elo0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h6, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h52, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h54, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h56, hlam, p183_1]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h7, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h53, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h55, hlam, p183_0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p183_1, u3elo0]
                                      · have p183_0 := h183c.1
                                        have p183_1 := h183c.2.1
                                        have p183_2 := h183c.2.2.1
                                        have p183_3 := h183c.2.2.2
                                        linarith only [hlam, p183_0]
                                    · linarith only [h182, hlam, ht01, ht12, u2elo0]
                                    · linarith only [h182, hlam, ht01, ht12, ht23, u3elo0]
                                    · linarith only [h182, hc05, hlam, p58_1]
                                    · linarith only [h182, h5, hlam, ht01, ht12, u2elo0]
                                  · linarith only [h181, h8, hlam]
                              · linarith only [h178, h6, hlam]
                            · linarith only [h177, h4, hlam]
                          · linarith only [h176, h2, hlam]
                        · have p58_0 := h58c.1
                          have p58_1 := h58c.2.1
                          have p58_2 := h58c.2.2.1
                          have p58_3 := h58c.2.2.2
                          linarith only [hlam, p58_0]
                    · linarith only [h1, h53, h55, hc23, hlam, hphi, u3elo0]
                  · linarith only [h54, h6, hc23, hlam, hphi, u3elo0]
                · linarith only [h53, h7, hc13, hlam, hphi, u3elo0]
              · linarith only [h51, h52, h6, hc23, hlam, hphi, u3elo0]
            · linarith only [h3, h51, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h243 | h243
          · linarith only [h243, h6, h7, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h245 | h245
            · rcases m.htr 1 3 4 (by decide) (by decide) with h246 | h246
              · rcases m.htr 1 3 5 (by decide) (by decide) with h247 | h247
                · linarith only [h247, h7, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h249 | h249
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h250 | h250
                    · linarith only [h1, h245, h250, h7, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h252 | h252
                      · linarith only [h0, h243, h245, h249, h252, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h0bigk with h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [hlam, p254_0]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [h249, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p254_1]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          rcases p254_3 (m.d 0 1) (by simp) with h257 | h257
                          · rcases p254_3 (m.d 0 2) (by simp) with h258 | h258
                            · linarith only [h0, h258, hlam]
                            · linarith only [h258, h3, hlam]
                          · linarith only [h1, h257, hlam]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          rcases p254_3 (m.d 0 1) (by simp) with h262 | h262
                          · rcases p254_3 (m.d 0 2) (by simp) with h263 | h263
                            · linarith only [h0, h263, hlam]
                            · linarith only [h263, h4, hlam]
                          · linarith only [h2, h262, hlam]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          rcases p254_3 (m.d 0 1) (by simp) with h267 | h267
                          · rcases p254_3 (m.d 0 2) (by simp) with h268 | h268
                            · linarith only [h0, h268, hlam]
                            · linarith only [h268, h5, hlam]
                          · linarith only [h267, hlam, p254_0]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [h0, hlam, p254_0]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [hlam, p254_0]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [h249, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p254_1, u2elo0]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          rcases p254_3 (m.d 0 1) (by simp) with h275 | h275
                          · rcases p254_3 (m.d 0 2) (by simp) with h276 | h276
                            · rcases p254_3 (m.d 0 3) (by simp) with h277 | h277
                              · linarith only [h277, h3, hlam]
                              · linarith only [h277, h6, hlam]
                            · linarith only [h276, h4, hlam]
                          · linarith only [h2, h275, hlam]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [h1, h245, h249, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p254_1, u2elo0]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [h1, hlam, p254_1]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [h3, hlam, p254_1]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [hlam, p254_0]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [h2, h246, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p254_1, u3elo4]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [h7, hlam, p254_1]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [h2, hlam, p254_0]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [h4, hlam, p254_0]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [h6, hlam, p254_0]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [hlam, p254_0]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [h243, hlam, p254_0]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [h1, h245, h249, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p254_1]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [h5, hlam, p254_1]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [h1, h245, h249, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p254_1, u2elo0]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          rcases p254_3 (m.d 0 1) (by simp) with h296 | h296
                          · rcases p254_3 (m.d 0 2) (by simp) with h297 | h297
                            · rcases p254_3 (m.d 0 3) (by simp) with h298 | h298
                              · linarith only [h298, h7, hlam]
                              · linarith only [h298, h6, hlam]
                            · linarith only [h297, h4, hlam]
                          · linarith only [h2, h296, hlam]
                        · have p254_0 := h254c.1
                          have p254_1 := h254c.2.1
                          have p254_2 := h254c.2.2.1
                          have p254_3 := h254c.2.2.2
                          linarith only [hlam, p254_0]
                  · linarith only [h249, h6, hc23, hlam, hphi, u3elo0]
              · linarith only [h245, h246, h6, h7, hc23, hlam, hphi, u3elo4]
            · linarith only [h245, h3, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h307 | h307
        · rcases m.htr 0 4 5 (by decide) (by decide) with h308 | h308
          · rcases m.htr 1 2 3 (by decide) (by decide) with h309 | h309
            · rcases m.htr 1 3 4 (by decide) (by decide) with h310 | h310
              · linarith only [h310, h6, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h312 | h312
                · rcases m.htr 2 3 4 (by decide) (by decide) with h313 | h313
                  · linarith only [h1, h309, h312, h313, h6, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h315 | h315
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h316 | h316
                      · rcases h0bigk with h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h0, h309, h315, h316, hc01, hc45, hlam, hphi, ht0b, ht5b, p317_1]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          rcases p317_3 (m.d 0 1) (by simp) with h320 | h320
                          · rcases p317_3 (m.d 0 2) (by simp) with h321 | h321
                            · linarith only [h0, h321, hlam]
                            · linarith only [h3, h321, hlam]
                          · linarith only [h1, h320, hlam]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          rcases p317_3 (m.d 0 1) (by simp) with h325 | h325
                          · rcases p317_3 (m.d 0 2) (by simp) with h326 | h326
                            · linarith only [h0, h326, hlam]
                            · linarith only [h326, h4, hlam]
                          · linarith only [h2, h325, hlam]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          rcases p317_3 (m.d 0 1) (by simp) with h330 | h330
                          · rcases p317_3 (m.d 0 2) (by simp) with h331 | h331
                            · linarith only [h0, h331, hlam]
                            · linarith only [h331, h5, hlam]
                          · linarith only [h330, hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h0, hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h1, h309, h315, h316, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p317_1, u2elo0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h1, h309, h315, h316, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p317_1, u2elo0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          rcases p317_3 (m.d 0 1) (by simp) with h339 | h339
                          · rcases p317_3 (m.d 0 2) (by simp) with h340 | h340
                            · rcases p317_3 (m.d 0 3) (by simp) with h341 | h341
                              · linarith only [h3, h341, hlam]
                              · linarith only [h307, h341, hlam]
                            · linarith only [h340, h5, hlam]
                          · linarith only [h339, hc01, hlam, hphi, ht12, p317_1, u2elo0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h1, hlam, p317_1]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h3, hlam, p317_1]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h6, hlam, p317_1]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h5, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p317_1, u3elo3]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h2, hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h4, hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h6, hc03, hlam, hphi, p317_1, u3elo3]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          rcases p317_3 (m.d 0 1) (by simp) with h355 | h355
                          · rcases p317_3 (m.d 0 2) (by simp) with h356 | h356
                            · rcases p317_3 (m.d 0 3) (by simp) with h357 | h357
                              · linarith only [h357, h6, hlam]
                              · linarith only [h307, h357, hlam]
                            · linarith only [h356, h5, hlam]
                          · linarith only [h0, h309, h315, h316, h355, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h0, h307, h309, h315, h316, hc03, hc45, hlam, hphi, ht0b, ht5b, p317_1]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h5, hlam, p317_1]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h307, hlam, p317_0]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [h308, hlam, p317_1]
                        · have p317_0 := h317c.1
                          have p317_1 := h317c.2.1
                          have p317_2 := h317c.2.2.1
                          have p317_3 := h317c.2.2.2
                          linarith only [hlam, p317_0]
                      · linarith only [h308, h316, h6, hlam]
                    · linarith only [h307, h315, h6, hc23, hlam, hphi, u3elo3]
                · linarith only [h307, h309, h312, h6, hc23, hlam, hphi, u3elo3]
            · linarith only [h3, h309, hc12, hlam, hphi, u2elo0]
          · linarith only [h307, h308, h6, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h372 | h372
          · rcases m.htr 1 2 3 (by decide) (by decide) with h373 | h373
            · rcases m.htr 1 3 4 (by decide) (by decide) with h374 | h374
              · linarith only [h374, h6, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h376 | h376
                · linarith only [h1, h307, h376, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h378 | h378
                  · linarith only [h1, h373, h378, h6, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h380 | h380
                    · linarith only [h1, h307, h373, h380, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h382 | h382
                      · rcases h0bigk with h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [hlam, p383_0]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          rcases p383_3 (m.d 0 1) (by simp) with h385 | h385
                          · rcases p383_3 (m.d 0 2) (by simp) with h386 | h386
                            · linarith only [h0, h386, hlam]
                            · rcases p383_3 (m.d 0 3) (by simp) with h388 | h388
                              · linarith only [h1, h388, hlam]
                              · rcases p383_3 (m.d 0 4) (by simp) with h390 | h390
                                · linarith only [h2, h390, hlam]
                                · rcases p383_3 (m.d 0 5) (by simp) with h392 | h392
                                  · linarith only [h2, h372, h392, hlam]
                                  · rcases h0emin with h394 | h394 | h394 | h394 | h394
                                    · rcases h3bigk with h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [hlam, p395_0]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [h307, h373, h382, hc23, hlam, hphi, p395_1, u3elo3]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [h307, h382, hc23, hlam, hphi, p395_1, u3elo3]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [h6, hlam, p395_0]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [h307, hlam, p395_0]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [h1, hlam, p395_0]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [hlam, p395_0]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [hc23, hlam, hphi, p395_1, u3elo1]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [h374, hlam, p395_0]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [h376, hlam, p395_0]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [h3, hlam, p395_0]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [h373, hlam, p395_0]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [hlam, p395_0]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [h378, hlam, p395_0]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [h380, hlam, p395_0]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [hc03, hlam, hphi, p395_1, u3elo3]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [h373, hc23, hlam, hphi, p395_1, u3elo3]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [hc23, hlam, hphi, p395_1, u3elo3]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [hlam, p395_0]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [h1, h307, h373, hc23, hlam, hphi, p395_1, u3elo3]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [h1, h373, hc23, hlam, hphi, p395_1, u3elo4]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [h373, hc23, hlam, hphi, p395_1, u3elo4]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [hc23, hlam, hphi, p395_1, u3elo4]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [h382, hlam, p395_0]
                                      · have p395_0 := h395c.1
                                        have p395_1 := h395c.2.1
                                        have p395_2 := h395c.2.2.1
                                        have p395_3 := h395c.2.2.2
                                        linarith only [hlam, p395_0]
                                    · linarith only [h394, hc01, hlam, p383_1]
                                    · linarith only [h394, hlam, ht01, ht12, ht23, u3elo0]
                                    · linarith only [h394, h4, hc01, hlam, p383_1]
                                    · linarith only [h372, h394, h4, hc01, hlam, p383_1]
                          · linarith only [h0, h385, hlam]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          rcases p383_3 (m.d 0 1) (by simp) with h426 | h426
                          · rcases p383_3 (m.d 0 2) (by simp) with h427 | h427
                            · linarith only [h0, h427, hlam]
                            · linarith only [h3, h427, hlam]
                          · linarith only [h1, h426, hlam]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          rcases p383_3 (m.d 0 1) (by simp) with h431 | h431
                          · rcases p383_3 (m.d 0 2) (by simp) with h432 | h432
                            · linarith only [h0, h432, hlam]
                            · linarith only [h4, h432, hlam]
                          · linarith only [h2, h431, hlam]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          rcases p383_3 (m.d 0 1) (by simp) with h436 | h436
                          · rcases p383_3 (m.d 0 2) (by simp) with h437 | h437
                            · linarith only [h0, h437, hlam]
                            · linarith only [h437, h5, hlam]
                          · linarith only [h436, hlam, p383_0]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [h0, hlam, p383_0]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [hlam, p383_0]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          rcases p383_3 (m.d 0 1) (by simp) with h443 | h443
                          · rcases p383_3 (m.d 0 2) (by simp) with h444 | h444
                            · rcases p383_3 (m.d 0 3) (by simp) with h445 | h445
                              · linarith only [h3, h445, hlam]
                              · rcases p383_3 (m.d 0 4) (by simp) with h447 | h447
                                · linarith only [h4, h447, hlam]
                                · linarith only [h447, h6, hlam]
                            · linarith only [h3, h444, hlam]
                          · linarith only [h1, h443, hlam]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [h372, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p383_1, u2elo0]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          rcases p383_3 (m.d 0 1) (by simp) with h453 | h453
                          · rcases p383_3 (m.d 0 2) (by simp) with h454 | h454
                            · rcases p383_3 (m.d 0 3) (by simp) with h455 | h455
                              · linarith only [h3, h455, hlam]
                              · rcases p383_3 (m.d 0 4) (by simp) with h457 | h457
                                · linarith only [h4, h457, hlam]
                                · linarith only [h372, h457, hlam]
                            · linarith only [h454, h5, hlam]
                          · linarith only [h453, hc01, hlam, hphi, ht12, p383_1, u2elo0]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [h1, hlam, p383_1]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [h3, hlam, p383_1]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [hlam, p383_0]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [h6, hlam, p383_1]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [h307, hlam, p383_1]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [h2, hlam, p383_0]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [h4, hlam, p383_0]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [h1, h373, h6, hc23, hlam, hphi, p383_1, u3elo3]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [hlam, p383_0]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [h1, h307, h373, h6, hc23, hlam, hphi, p383_1, u3elo3]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [h0, h373, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p383_1]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [h5, hlam, p383_1]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [h1, h307, h373, h382, hc23, hlam, hphi, p383_1, u3elo3]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [h372, hlam, p383_1]
                        · have p383_0 := h383c.1
                          have p383_1 := h383c.2.1
                          have p383_2 := h383c.2.2.1
                          have p383_3 := h383c.2.2.2
                          linarith only [hlam, p383_0]
                      · linarith only [h372, h382, h6, hlam]
            · linarith only [h3, h373, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h479 | h479
            · rcases m.htr 1 3 4 (by decide) (by decide) with h480 | h480
              · linarith only [h1, h480, h6, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h482 | h482
                · linarith only [h1, h307, h482, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h484 | h484
                  · linarith only [h1, h479, h484, h6, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h486 | h486
                    · linarith only [h1, h307, h479, h486, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h488 | h488
                      · linarith only [h2, h372, h480, h488, hc13, hlam, hphi, u3elo3]
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
                          rcases p490_3 (m.d 0 1) (by simp) with h492 | h492
                          · rcases p490_3 (m.d 0 2) (by simp) with h493 | h493
                            · linarith only [h0, h493, hlam]
                            · rcases p490_3 (m.d 0 3) (by simp) with h495 | h495
                              · linarith only [h1, h495, hlam]
                              · rcases p490_3 (m.d 0 4) (by simp) with h497 | h497
                                · linarith only [h2, h497, hlam]
                                · rcases p490_3 (m.d 0 5) (by simp) with h499 | h499
                                  · linarith only [h499, h5, hlam, p490_1]
                                  · rcases h0emin with h501 | h501 | h501 | h501 | h501
                                    · rcases h3bigk with h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [hlam, p502_0]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h479, h488, h6, hc23, hc45, hlam, hphi, ht34, p502_1]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h488, h6, hc23, hc45, hlam, hphi, ht34, p502_1]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h6, hlam, p502_0]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h307, hlam, p502_0]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h1, hlam, p502_0]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [hlam, p502_0]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [hc23, hlam, hphi, p502_1, u3elo1]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h480, hlam, p502_0]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h482, hlam, p502_0]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h3, hlam, p502_0]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h479, hlam, p502_0]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [hlam, p502_0]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h484, hlam, p502_0]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h486, hlam, p502_0]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h488, hc03, hc45, hlam, hphi, ht34, p502_1]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h479, h488, hc23, hc45, hlam, hphi, ht34, p502_1]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h488, hc23, hc45, hlam, hphi, ht34, p502_1]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [hlam, p502_0]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h488, hlam, p502_1]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h1, h479, hc23, hlam, hphi, p502_1, u3elo4]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h479, hc23, hlam, hphi, p502_1, u3elo4]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [hc23, hlam, hphi, p502_1, u3elo4]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [h1, h479, h6, hc23, hlam, hphi, p502_1, u3elo4]
                                      · have p502_0 := h502c.1
                                        have p502_1 := h502c.2.1
                                        have p502_2 := h502c.2.2.1
                                        have p502_3 := h502c.2.2.2
                                        linarith only [hlam, p502_0]
                                    · linarith only [h501, hc01, hlam, p490_1]
                                    · linarith only [h501, hlam, ht01, ht12, ht23, u3elo0]
                                    · linarith only [h4, h501, hc01, hlam, p490_1]
                                    · linarith only [h5, h501, hc01, hlam, p490_1]
                          · linarith only [h0, h492, hlam]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          rcases p490_3 (m.d 0 1) (by simp) with h533 | h533
                          · rcases p490_3 (m.d 0 2) (by simp) with h534 | h534
                            · linarith only [h0, h534, hlam]
                            · linarith only [h3, h534, hlam]
                          · linarith only [h1, h533, hlam]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          rcases p490_3 (m.d 0 1) (by simp) with h538 | h538
                          · rcases p490_3 (m.d 0 2) (by simp) with h539 | h539
                            · linarith only [h0, h539, hlam]
                            · linarith only [h4, h539, hlam]
                          · linarith only [h2, h538, hlam]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          rcases p490_3 (m.d 0 1) (by simp) with h543 | h543
                          · rcases p490_3 (m.d 0 2) (by simp) with h544 | h544
                            · linarith only [h0, h544, hlam]
                            · linarith only [h5, h544, hlam]
                          · linarith only [h543, hlam, p490_0]
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
                          rcases p490_3 (m.d 0 1) (by simp) with h550 | h550
                          · rcases p490_3 (m.d 0 2) (by simp) with h551 | h551
                            · rcases p490_3 (m.d 0 3) (by simp) with h552 | h552
                              · linarith only [h3, h552, hlam]
                              · rcases p490_3 (m.d 0 4) (by simp) with h554 | h554
                                · linarith only [h4, h554, hlam]
                                · linarith only [h554, h6, hlam]
                            · linarith only [h3, h551, hlam]
                          · linarith only [h1, h550, hlam]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          rcases p490_3 (m.d 0 1) (by simp) with h559 | h559
                          · rcases p490_3 (m.d 0 2) (by simp) with h560 | h560
                            · rcases p490_3 (m.d 0 3) (by simp) with h561 | h561
                              · linarith only [h3, h561, hlam]
                              · rcases p490_3 (m.d 0 4) (by simp) with h563 | h563
                                · linarith only [h4, h563, hlam]
                                · rcases p490_3 (m.d 0 5) (by simp) with h565 | h565
                                  · linarith only [h5, h565, hlam]
                                  · linarith only [h372, h565, hlam]
                            · linarith only [h4, h560, hlam]
                          · linarith only [h2, h559, hlam]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          rcases p490_3 (m.d 0 1) (by simp) with h570 | h570
                          · rcases p490_3 (m.d 0 2) (by simp) with h571 | h571
                            · rcases p490_3 (m.d 0 3) (by simp) with h572 | h572
                              · linarith only [h3, h572, hlam]
                              · rcases p490_3 (m.d 0 4) (by simp) with h574 | h574
                                · linarith only [h4, h574, hlam]
                                · rcases p490_3 (m.d 0 5) (by simp) with h576 | h576
                                  · linarith only [h5, h576, hlam]
                                  · rcases h0emin with h578 | h578 | h578 | h578 | h578
                                    · rcases h3bigk with h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [hlam, p579_0]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h479, hc23, hlam, hphi, p579_1, u3elo0]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [hc23, hlam, hphi, p579_1, u3elo0]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h6, hlam, p579_0]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h307, hlam, p579_0]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h1, hlam, p579_0]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [hlam, p579_0]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h2, h372, h480, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p490_1, p579_1, u2elo0]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h480, hlam, p579_0]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h482, hlam, p579_0]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h3, hlam, p579_0]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h479, hlam, p579_0]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [hlam, p579_0]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h484, hlam, p579_0]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h486, hlam, p579_0]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h488, hc03, hc45, hlam, hphi, ht34, p579_1]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h488, hc13, hc45, hlam, hphi, ht34, p579_1]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h488, hc23, hc45, hlam, hphi, ht34, p579_1]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [hlam, p579_0]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h488, hlam, p579_1]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h1, h479, hc23, hlam, hphi, p579_1, u3elo4]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h479, hc23, hlam, hphi, p579_1, u3elo4]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [hc23, hlam, hphi, p579_1, u3elo4]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [h1, h479, h6, hc23, hlam, hphi, p579_1, u3elo4]
                                      · have p579_0 := h579c.1
                                        have p579_1 := h579c.2.1
                                        have p579_2 := h579c.2.2.1
                                        have p579_3 := h579c.2.2.2
                                        linarith only [hlam, p579_0]
                                    · linarith only [h578, hlam, ht01, ht12, u2elo0]
                                    · linarith only [h578, hlam, ht01, ht12, ht23, u3elo0]
                                    · linarith only [h372, h578, hlam, ht01, ht12, p490_1, u2elo0]
                                    · linarith only [h578, hlam, ht01, ht12, p490_1, u2elo0]
                            · linarith only [h5, h571, hlam]
                          · linarith only [h570, hc01, hlam, hphi, ht12, p490_1, u2elo0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h1, hlam, p490_1]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h3, hlam, p490_1]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [hlam, p490_0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h6, hlam, p490_1]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h307, hlam, p490_1]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h2, hlam, p490_0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h4, hlam, p490_0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h1, h479, h488, h6, hc23, hc45, hlam, hphi, ht34, p490_1]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [hlam, p490_0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h372, hlam, p490_0]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h0, h479, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p490_1]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h5, hlam, p490_1]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h1, h307, h479, hc23, hlam, hphi, p490_1, u3elo4]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [h307, h4, h484, hc23, hlam, hphi, p490_1, u3elo4]
                        · have p490_0 := h490c.1
                          have p490_1 := h490c.2.1
                          have p490_2 := h490c.2.2.1
                          have p490_3 := h490c.2.2.2
                          linarith only [hlam, p490_0]
            · linarith only [h3, h479, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h627 | h627
      · rcases m.htr 0 3 5 (by decide) (by decide) with h628 | h628
        · linarith only [h3, h5, h628, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h630 | h630
          · linarith only [h4, h5, h630, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h632 | h632
            · rcases m.htr 1 3 4 (by decide) (by decide) with h633 | h633
              · rcases m.htr 1 3 5 (by decide) (by decide) with h634 | h634
                · linarith only [h628, h634, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h636 | h636
                  · linarith only [h0, h5, h632, h636, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · linarith only [h1, h628, h633, h636, hc23, hlam, hphi, u3elo4]
              · linarith only [h627, h628, h633, hc13, hlam, hphi, u3elo4]
            · linarith only [h3, h5, h632, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h641 | h641
        · linarith only [h3, h5, h627, h641, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h643 | h643
          · linarith only [h4, h5, h643, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h645 | h645
            · rcases m.htr 1 3 4 (by decide) (by decide) with h646 | h646
              · linarith only [h627, h646, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h648 | h648
                · linarith only [h1, h3, h5, h641, h648, hc23, hlam, hphi, u3elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h650 | h650
                  · linarith only [h0, h627, h645, h650, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h652 | h652
                    · linarith only [h0, h5, h641, h645, h652, hlam]
                    · linarith only [h0, h5, h645, h652, hc23, hlam, hphi, u3elo4]
            · linarith only [h3, h5, h645, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h656 | h656
    · rcases m.htr 0 3 4 (by decide) (by decide) with h657 | h657
      · linarith only [h3, h4, h657, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h659 | h659
        · rcases m.htr 0 4 5 (by decide) (by decide) with h660 | h660
          · rcases m.htr 1 2 3 (by decide) (by decide) with h661 | h661
            · rcases m.htr 1 3 4 (by decide) (by decide) with h662 | h662
              · linarith only [h1, h657, h662, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h664 | h664
                · rcases m.htr 2 3 4 (by decide) (by decide) with h665 | h665
                  · linarith only [h0, h4, h657, h661, h665, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h4, h661, h665, hc23, hlam, hphi, u3elo3]
                · linarith only [h657, h659, h664, hc13, hlam, hphi, u3elo3]
            · linarith only [h3, h4, h661, hc12, hlam, hphi, u2elo3]
          · linarith only [h3, h4, h657, h659, h660, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h671 | h671
          · rcases m.htr 1 2 3 (by decide) (by decide) with h672 | h672
            · rcases m.htr 1 3 4 (by decide) (by decide) with h673 | h673
              · linarith only [h657, h673, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h675 | h675
                · linarith only [h1, h659, h675, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h677 | h677
                  · linarith only [h0, h1, h657, h672, h677, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h0, h4, h672, h677, hc23, hlam, hphi, u3elo3]
            · linarith only [h3, h4, h672, hc12, hlam, hphi, u2elo3]
          · linarith only [h4, h656, h671, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h682 | h682
      · linarith only [h3, h4, h682, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h684 | h684
        · linarith only [h3, h656, h684, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h686 | h686
          · rcases m.htr 1 2 3 (by decide) (by decide) with h687 | h687
            · rcases m.htr 1 3 4 (by decide) (by decide) with h688 | h688
              · linarith only [h1, h682, h688, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h690 | h690
                · linarith only [h1, h684, h690, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h692 | h692
                  · linarith only [h0, h4, h682, h687, h692, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h3, h4, h692, hc23, hlam, hphi, u3elo3]
            · linarith only [h3, h4, h687, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h696 | h696
            · rcases m.htr 1 3 4 (by decide) (by decide) with h697 | h697
              · linarith only [h1, h682, h697, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h699 | h699
                · linarith only [h1, h684, h699, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h701 | h701
                  · linarith only [h0, h4, h682, h696, h701, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h3, h4, h701, hc23, hlam, hphi, u3elo3]
            · linarith only [h3, h4, h696, hc12, hlam, hphi, u2elo3]

end R2N4
