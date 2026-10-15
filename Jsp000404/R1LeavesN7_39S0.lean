import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h14, h17, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h14, h16, h17, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                    · linarith only [h16, h20, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                    · rcases h1bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [hlam, p22_0]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h15, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p22_1]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h11, h13, h14, h16, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h13, h14, h16, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        rcases p22_3 (m.d 0 1) (by simp) with h27 | h27
                        · rcases p22_3 (m.d 1 2) (by simp) with h28 | h28
                          · linarith only [h0, h28, hlam]
                          · linarith only [h10, h28, hlam]
                        · linarith only [h27, hlam, p22_0]
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
                        linarith only [h11, h13, h14, h16, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22_1]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h0, h13, h14, h16, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h0, h13, h14, h16, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h1, hlam, p22_0]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h8, hlam, p22_1]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [hlam, p22_0]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h13, h14, h16, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22_1]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h1, h13, h14, h16, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p22_1, u3elo0]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h2, hlam, p22_0]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h9, hlam, p22_1]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h11, hlam, p22_0]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [hlam, p22_0]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h13, h14, h16, h2, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p22_1, u3elo0]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h3, hlam, p22_0]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h10, hlam, p22_1]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h12, hlam, p22_0]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h13, hlam, p22_0]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [hlam, p22_0]
                · linarith only [h15, h6, hc23, hlam, hphi, u3elo0]
              · linarith only [h14, h5, hc23, hlam, hphi, u3elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
              · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                · rcases m.htr 2 4 5 (by decide) (by decide) with h56 | h56
                  · linarith only [h13, h56, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
                    · linarith only [h13, h54, h58, h9, hlam]
                    · rcases h1bigk with h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h55, h58, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p60_1]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        rcases p60_3 (m.d 0 1) (by simp) with h63 | h63
                        · rcases p60_3 (m.d 1 2) (by simp) with h64 | h64
                          · linarith only [h0, h64, hlam]
                          · linarith only [h64, h8, hlam]
                        · linarith only [h63, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        rcases p60_3 (m.d 0 1) (by simp) with h68 | h68
                        · rcases p60_3 (m.d 1 2) (by simp) with h69 | h69
                          · linarith only [h0, h69, hlam]
                          · linarith only [h69, h9, hlam]
                        · linarith only [h68, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        rcases p60_3 (m.d 0 1) (by simp) with h73 | h73
                        · rcases p60_3 (m.d 1 2) (by simp) with h74 | h74
                          · linarith only [h0, h74, hlam]
                          · linarith only [h10, h74, hlam]
                        · linarith only [h73, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h0, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h0, h55, h58, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p60_1]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        rcases p60_3 (m.d 0 1) (by simp) with h81 | h81
                        · rcases p60_3 (m.d 1 2) (by simp) with h82 | h82
                          · rcases p60_3 (m.d 1 3) (by simp) with h83 | h83
                            · linarith only [h8, h83, hlam]
                            · linarith only [h11, h83, hlam]
                          · linarith only [h82, h9, hlam]
                        · linarith only [h2, h81, hlam]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        rcases p60_3 (m.d 0 1) (by simp) with h88 | h88
                        · rcases p60_3 (m.d 1 2) (by simp) with h89 | h89
                          · rcases p60_3 (m.d 1 3) (by simp) with h90 | h90
                            · linarith only [h8, h90, hlam]
                            · linarith only [h12, h90, hlam]
                          · linarith only [h10, h89, hlam]
                        · linarith only [h3, h88, hlam]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h1, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h8, hlam, p60_1]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        rcases p60_3 (m.d 0 1) (by simp) with h98 | h98
                        · rcases p60_3 (m.d 1 2) (by simp) with h99 | h99
                          · rcases p60_3 (m.d 1 3) (by simp) with h100 | h100
                            · rcases p60_3 (m.d 1 4) (by simp) with h101 | h101
                              · linarith only [h101, h11, hlam]
                              · rcases p60_3 (m.d 1 5) (by simp) with h103 | h103
                                · linarith only [h103, h12, hlam]
                                · linarith only [h103, h13, hlam]
                            · linarith only [h100, h11, hlam]
                          · linarith only [h9, h99, hlam]
                        · linarith only [h2, h98, hlam]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        rcases p60_3 (m.d 0 1) (by simp) with h109 | h109
                        · rcases p60_3 (m.d 1 2) (by simp) with h110 | h110
                          · rcases p60_3 (m.d 1 3) (by simp) with h111 | h111
                            · rcases p60_3 (m.d 1 4) (by simp) with h112 | h112
                              · linarith only [h11, h112, hlam]
                              · rcases p60_3 (m.d 1 5) (by simp) with h114 | h114
                                · linarith only [h114, h12, hlam]
                                · rcases h1emin with h116 | h116 | h116 | h116 | h116
                                  · rcases h5bigk with h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h13, h5, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p117_1, u3elo0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h5, h56, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p117_1, u3elo0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h5, h58, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p117_1, u3elo0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h5, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p117_1, u3elo0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h3, hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h3, h56, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p117_1]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h1, h58, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p117_1, p60_1, u3elo0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h13, hlam, p117_1]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h4, hlam, p117_1]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h10, hlam, p117_1]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h0, h4, h58, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p117_1]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h56, hlam, p117_1]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h6, hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h12, hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h55, hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h58, hlam, p117_1]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h7, hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h10, h5, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p117_1, u3elo0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h5, h55, h58, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p117_1, u3elo0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h5, h58, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p117_1, u3elo0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [hlam, p117_0]
                                  · rcases h5bigk with h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [hlam, p143_0]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h13, h5, h54, h7, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p143_1, u3elo0]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h5, h55, h58, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p143_1, u3elo0]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h5, h58, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p143_1, u3elo0]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h5, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p143_1, u3elo0]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h3, hlam, p143_0]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [hlam, p143_0]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h3, h55, h58, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p143_1]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h1, h58, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p143_1, p60_1, u3elo0]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h13, hlam, p143_1]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h4, hlam, p143_1]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h10, hlam, p143_1]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [hlam, p143_0]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h0, h4, h58, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p143_1]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h56, hlam, p143_1]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h6, hlam, p143_0]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h12, hlam, p143_0]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h55, hlam, p143_0]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [hlam, p143_0]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h58, hlam, p143_1]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h7, hlam, p143_0]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h10, h5, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p143_1, u3elo0]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h5, h55, h58, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p143_1, u3elo0]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [h5, h58, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p143_1, u3elo0]
                                    · have p143_0 := h143c.1
                                      have p143_1 := h143c.2.1
                                      have p143_2 := h143c.2.2.1
                                      have p143_3 := h143c.2.2.2
                                      linarith only [hlam, p143_0]
                                  · linarith only [h1, h116, hlam, ht12, ht23, u3elo0]
                                  · linarith only [h116, h2, h5, hlam, ht12, ht23, u3elo0]
                                  · linarith only [h116, h3, h5, h7, hlam, ht12, ht23, u3elo0]
                            · linarith only [h111, h12, hlam]
                          · linarith only [h10, h110, hlam]
                        · linarith only [h109, h3, hlam]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h2, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h9, hlam, p60_1]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h11, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h13, hlam, p60_1]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h3, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h10, hlam, p60_1]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h12, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h13, h5, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p60_1, u3elo0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [hlam, p60_0]
                · linarith only [h55, h6, hc23, hlam, hphi, u3elo0]
              · linarith only [h5, h54, hc23, hlam, hphi, u3elo0]
          · linarith only [h12, h6, hc13, hlam, hphi, u3elo0]
        · linarith only [h11, h5, h8, hc23, hlam, hphi, u3elo0]
      · linarith only [h10, h4, h5, h7, h8, hc23, hlam, hphi, u3elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h190 | h190
      · rcases m.htr 1 3 4 (by decide) (by decide) with h191 | h191
        · linarith only [h191, h8, h9, hlam]
        · linarith only [h191, h5, hc13, hlam, hphi, u3elo0]
      · linarith only [h190, h4, h5, h7, h8, hc23, hlam, hphi, u3elo0]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h195 | h195
    · rcases m.htr 1 2 5 (by decide) (by decide) with h196 | h196
      · rcases m.htr 1 3 4 (by decide) (by decide) with h197 | h197
        · rcases m.htr 1 3 5 (by decide) (by decide) with h198 | h198
          · rcases m.htr 1 4 5 (by decide) (by decide) with h199 | h199
            · rcases m.htr 2 3 4 (by decide) (by decide) with h200 | h200
              · rcases m.htr 2 3 5 (by decide) (by decide) with h201 | h201
                · rcases m.htr 2 4 5 (by decide) (by decide) with h202 | h202
                  · linarith only [h195, h202, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h195, h199, h202, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h201, h8, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h200, h8, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h207 | h207
              · rcases m.htr 2 3 5 (by decide) (by decide) with h208 | h208
                · rcases m.htr 2 4 5 (by decide) (by decide) with h209 | h209
                  · linarith only [h0, h195, h199, h209, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h211 | h211
                    · linarith only [h195, h199, h207, h211, h8, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · rcases h1bigk with h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        rcases p213_3 (m.d 0 1) (by simp) with h215 | h215
                        · rcases p213_3 (m.d 1 2) (by simp) with h216 | h216
                          · linarith only [h216, hlam, p213_0]
                          · rcases p213_3 (m.d 1 3) (by simp) with h218 | h218
                            · linarith only [h1, h218, hlam]
                            · linarith only [h218, h8, hlam]
                        · linarith only [h215, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        rcases p213_3 (m.d 0 1) (by simp) with h222 | h222
                        · rcases p213_3 (m.d 1 2) (by simp) with h223 | h223
                          · linarith only [h0, h223, hlam]
                          · rcases p213_3 (m.d 1 3) (by simp) with h225 | h225
                            · linarith only [h225, hlam, p213_0]
                            · rcases p213_3 (m.d 1 4) (by simp) with h227 | h227
                              · linarith only [h2, h227, hlam]
                              · rcases p213_3 (m.d 1 5) (by simp) with h229 | h229
                                · linarith only [h229, h3, hlam]
                                · rcases h1emin with h231 | h231 | h231 | h231 | h231
                                  · rcases h5bigk with h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [hlam, p232_0]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h5, h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p232_1, u3elo0]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h208, h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p232_1, u3elo0]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p232_1, u3elo0]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h195, h199, h207, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p232_1, u3elo0]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h3, hlam, p232_0]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [hlam, p232_0]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h208, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p232_1]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h196, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p232_1, u3elo2]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h199, hlam, p232_1]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h4, hlam, p232_1]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h196, hlam, p232_1]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [hlam, p232_0]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h0, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p232_1]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h209, hlam, p232_1]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h6, hlam, p232_0]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h198, hlam, p232_0]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h208, hlam, p232_0]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [hlam, p232_0]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h211, hlam, p232_1]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h7, hlam, p232_0]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h5, h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p232_1, u3elo0]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h208, h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p232_1, u3elo0]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p232_1, u3elo0]
                                    · have p232_0 := h232c.1
                                      have p232_1 := h232c.2.1
                                      have p232_2 := h232c.2.2.1
                                      have p232_3 := h232c.2.2.2
                                      linarith only [hlam, p232_0]
                                  · linarith only [h231, h8, hlam, ht12, ht23, u3elo2]
                                  · linarith only [h231, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p213_1]
                                  · linarith only [h2, h231, h5, hlam, ht12, ht23, u3elo0]
                                  · linarith only [h231, h3, h5, h7, hlam, ht12, ht23, u3elo0]
                        · linarith only [h222, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        rcases p213_3 (m.d 0 1) (by simp) with h263 | h263
                        · rcases p213_3 (m.d 1 2) (by simp) with h264 | h264
                          · linarith only [h0, h264, hlam]
                          · linarith only [h195, h264, hlam]
                        · linarith only [h263, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        rcases p213_3 (m.d 0 1) (by simp) with h268 | h268
                        · rcases p213_3 (m.d 1 2) (by simp) with h269 | h269
                          · linarith only [h0, h269, hlam]
                          · linarith only [h196, h269, hlam]
                        · linarith only [h268, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h0, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h8, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h195, h207, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p213_1, u3elo2]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h8, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p213_1, u3elo2]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h1, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [hc12, hlam, hphi, ht23, p213_1, u3elo1]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        rcases p213_3 (m.d 0 1) (by simp) with h281 | h281
                        · rcases p213_3 (m.d 1 2) (by simp) with h282 | h282
                          · linarith only [h282, h8, hlam]
                          · linarith only [h195, h282, hlam]
                        · linarith only [h2, h281, hlam]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        rcases p213_3 (m.d 0 1) (by simp) with h286 | h286
                        · rcases p213_3 (m.d 1 2) (by simp) with h287 | h287
                          · linarith only [h287, h8, hlam]
                          · linarith only [h196, h287, hlam]
                        · linarith only [h286, h3, hlam]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h2, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h195, hlam, p213_1]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h197, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h199, hlam, p213_1]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h3, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h196, hlam, p213_1]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h198, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h195, h196, h207, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p213_1, u3elo2]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [hlam, p213_0]
                · linarith only [h208, h8, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h207, h5, h8, hc13, hlam, hphi, u3elo0]
          · linarith only [h195, h198, h6, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
        · linarith only [h195, h197, h5, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h305 | h305
        · rcases m.htr 1 3 5 (by decide) (by decide) with h306 | h306
          · rcases m.htr 1 4 5 (by decide) (by decide) with h307 | h307
            · linarith only [h195, h196, h307, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h309 | h309
              · rcases m.htr 2 3 5 (by decide) (by decide) with h310 | h310
                · rcases m.htr 2 4 5 (by decide) (by decide) with h311 | h311
                  · linarith only [h195, h196, h307, h311, h4, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h196, h311, h5, h7, hc12, hlam, hphi, ht23, u3elo0]
                · linarith only [h306, h307, h310, h5, h7, hc23, hlam, hphi, u3elo0]
              · linarith only [h309, h5, h8, hc13, hlam, hphi, u3elo0]
          · linarith only [h306, h6, h8, hc12, hlam, hphi, ht23, u3elo0]
        · linarith only [h195, h305, h5, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h318 | h318
      · rcases m.htr 1 3 4 (by decide) (by decide) with h319 | h319
        · rcases m.htr 1 3 5 (by decide) (by decide) with h320 | h320
          · rcases m.htr 1 4 5 (by decide) (by decide) with h321 | h321
            · rcases m.htr 2 3 4 (by decide) (by decide) with h322 | h322
              · rcases m.htr 2 3 5 (by decide) (by decide) with h323 | h323
                · rcases m.htr 2 4 5 (by decide) (by decide) with h324 | h324
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h325 | h325
                    · rcases h1bigk with h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [hlam, p326_0]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        rcases p326_3 (m.d 0 1) (by simp) with h328 | h328
                        · rcases p326_3 (m.d 1 2) (by simp) with h329 | h329
                          · linarith only [h329, hlam, p326_0]
                          · rcases p326_3 (m.d 1 3) (by simp) with h331 | h331
                            · linarith only [h1, h331, hlam]
                            · linarith only [h331, h8, hlam]
                        · linarith only [h328, hlam, p326_0]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [h319, h325, hc01, hc45, hlam, hphi, ht0b, ht5b, p326_1]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        rcases p326_3 (m.d 0 1) (by simp) with h336 | h336
                        · rcases p326_3 (m.d 1 2) (by simp) with h337 | h337
                          · linarith only [h0, h337, hlam]
                          · rcases p326_3 (m.d 1 3) (by simp) with h339 | h339
                            · linarith only [h1, h339, hlam]
                            · linarith only [h319, h339, hlam]
                        · linarith only [h336, hlam, p326_0]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        rcases p326_3 (m.d 0 1) (by simp) with h343 | h343
                        · rcases p326_3 (m.d 1 2) (by simp) with h344 | h344
                          · linarith only [h0, h344, hlam]
                          · linarith only [h318, h344, hlam]
                        · linarith only [h343, hlam, p326_0]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [h0, hlam, p326_0]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [hlam, p326_0]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [h8, hlam, p326_0]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [h195, hlam, p326_0]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [h195, h322, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p326_1, u3elo2]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [h1, hlam, p326_0]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [hc12, hlam, hphi, ht23, p326_1, u3elo1]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [hlam, p326_0]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [h1, h195, h318, h323, h325, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p326_1, u3elo0]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        rcases p326_3 (m.d 0 1) (by simp) with h357 | h357
                        · rcases p326_3 (m.d 1 2) (by simp) with h358 | h358
                          · linarith only [h358, h8, hlam]
                          · linarith only [h318, h358, hlam]
                        · linarith only [h3, h357, hlam]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [h2, hlam, p326_0]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [h2, h318, h323, h325, hc01, hc45, hlam, hphi, ht0b, ht5b, p326_1]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [h319, hlam, p326_0]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [hlam, p326_0]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        rcases p326_3 (m.d 0 1) (by simp) with h366 | h366
                        · rcases p326_3 (m.d 1 2) (by simp) with h367 | h367
                          · linarith only [h195, h367, hlam]
                          · linarith only [h318, h367, hlam]
                        · linarith only [h3, h366, hlam]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [h3, hlam, p326_0]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [h318, hlam, p326_1]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [h320, hlam, p326_0]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [h321, hlam, p326_0]
                      · have p326_0 := h326c.1
                        have p326_1 := h326c.2.1
                        have p326_2 := h326c.2.2.1
                        have p326_3 := h326c.2.2.2
                        linarith only [hlam, p326_0]
                    · linarith only [h195, h318, h322, h324, h325, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · linarith only [h195, h324, h5, h7, hc12, hlam, hphi, ht23, u3elo0]
                · linarith only [h323, h6, hc23, hlam, hphi, u3elo0]
              · linarith only [h322, h5, h8, hc13, hlam, hphi, u3elo0]
            · linarith only [h195, h318, h321, h5, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
          · linarith only [h195, h318, h319, h320, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
        · linarith only [h319, h5, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h383 | h383
        · rcases m.htr 1 3 5 (by decide) (by decide) with h384 | h384
          · rcases m.htr 1 4 5 (by decide) (by decide) with h385 | h385
            · rcases m.htr 2 3 4 (by decide) (by decide) with h386 | h386
              · rcases m.htr 2 3 5 (by decide) (by decide) with h387 | h387
                · rcases m.htr 2 4 5 (by decide) (by decide) with h388 | h388
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h389 | h389
                    · rcases h1bigk with h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        rcases p390_3 (m.d 0 1) (by simp) with h392 | h392
                        · rcases p390_3 (m.d 1 2) (by simp) with h393 | h393
                          · linarith only [h393, hlam, p390_0]
                          · rcases p390_3 (m.d 1 3) (by simp) with h395 | h395
                            · linarith only [h1, h395, hlam]
                            · linarith only [h395, h8, hlam]
                        · linarith only [h392, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h383, h389, hc01, hc45, hlam, hphi, ht0b, ht5b, p390_1]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        rcases p390_3 (m.d 0 1) (by simp) with h400 | h400
                        · rcases p390_3 (m.d 1 2) (by simp) with h401 | h401
                          · linarith only [h0, h401, hlam]
                          · rcases p390_3 (m.d 1 3) (by simp) with h403 | h403
                            · linarith only [h1, h403, hlam]
                            · linarith only [h383, h403, hlam]
                        · linarith only [h400, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        rcases p390_3 (m.d 0 1) (by simp) with h407 | h407
                        · rcases p390_3 (m.d 1 2) (by simp) with h408 | h408
                          · linarith only [h0, h408, hlam]
                          · rcases p390_3 (m.d 1 3) (by simp) with h410 | h410
                            · linarith only [h1, h410, hlam]
                            · linarith only [h384, h410, hlam]
                        · linarith only [h407, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h0, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h8, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h195, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h318, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h1, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [hc12, hlam, hphi, ht23, p390_1, u3elo1]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h318, h385, h8, hc12, hlam, hphi, ht23, p390_1, u3elo2]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h318, h8, hc12, hlam, hphi, ht23, p390_1, u3elo2]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h2, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h2, h5, hc12, hlam, hphi, ht23, p390_1, u3elo0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h383, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h2, h318, h5, hc12, hlam, hphi, ht23, p390_1, u3elo0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h3, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h3, h5, h7, hc12, hlam, hphi, ht23, p390_1, u3elo0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h384, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h385, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [hlam, p390_0]
                    · rcases h1bigk with h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [hlam, p434_0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        rcases p434_3 (m.d 0 1) (by simp) with h436 | h436
                        · rcases p434_3 (m.d 1 2) (by simp) with h437 | h437
                          · linarith only [h437, hlam, p434_0]
                          · rcases p434_3 (m.d 1 3) (by simp) with h439 | h439
                            · linarith only [h1, h439, hlam]
                            · linarith only [h439, h8, hlam]
                        · linarith only [h436, hlam, p434_0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [h383, h385, h389, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p434_1]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [h385, h389, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p434_1]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        rcases p434_3 (m.d 0 1) (by simp) with h445 | h445
                        · rcases p434_3 (m.d 1 2) (by simp) with h446 | h446
                          · linarith only [h0, h446, hlam]
                          · rcases p434_3 (m.d 1 3) (by simp) with h448 | h448
                            · linarith only [h1, h448, hlam]
                            · linarith only [h384, h448, hlam]
                        · linarith only [h445, hlam, p434_0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [h0, hlam, p434_0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [hlam, p434_0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [h8, hlam, p434_0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [h195, hlam, p434_0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [h318, hlam, p434_0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [h1, hlam, p434_0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [hc12, hlam, hphi, ht23, p434_1, u3elo1]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [hlam, p434_0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [h1, h385, h389, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p434_1, u3elo0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [h1, h318, hc12, hlam, hphi, ht23, p434_1, u3elo0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [h2, hlam, p434_0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [h2, h5, hc12, hlam, hphi, ht23, p434_1, u3elo0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [h383, hlam, p434_0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [hlam, p434_0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [h2, h318, h5, hc12, hlam, hphi, ht23, p434_1, u3elo0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [h3, hlam, p434_0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [h3, h5, h7, hc12, hlam, hphi, ht23, p434_1, u3elo0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [h384, hlam, p434_0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [h385, hlam, p434_0]
                      · have p434_0 := h434c.1
                        have p434_1 := h434c.2.1
                        have p434_2 := h434c.2.2.1
                        have p434_3 := h434c.2.2.2
                        linarith only [hlam, p434_0]
                  · linarith only [h195, h388, h5, h7, hc12, hlam, hphi, ht23, u3elo0]
                · linarith only [h1, h384, h387, hc23, hlam, hphi, u3elo0]
              · linarith only [h386, h5, h8, hc13, hlam, hphi, u3elo0]
            · linarith only [h195, h385, h5, h7, hc12, hlam, hphi, ht23, u3elo0]
          · linarith only [h383, h384, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
        · linarith only [h383, h5, hc13, hlam, hphi, u3elo0]

end R2N4
